import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableGlobalRootRegularity4D
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Instances.Matrix

/-!
# Scalar coefficient reduction for the positive diagonalizable root

For a four-by-four root, Cayley--Hamilton reconstructs the whole matrix from
its square and the four nonleading coefficients of its characteristic
polynomial.  On the positive diagonalizable locus the reconstruction
denominator is invertible.  Consequently continuity of the global matrix
selector is equivalent to continuity of only these four scalar symmetric
spectral coefficients.

This removes eigenbases and eigenvalue orderings from the remaining analytic
frontier.  Mathlib currently has no theorem giving continuity of the roots of
a varying real polynomial as an unordered multiset, so the scalar coefficient
map remains the exact residual.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableRootCoefficientRegularity4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableGlobalRootRegularity4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

/-- The four nonleading characteristic coefficients of the selected root. -/
def positiveRootCharpolyCoefficients
    (target : positiveDiagonalizableLocus) : Fin 4 → Real :=
  fun index =>
    (positiveDiagonalizableGlobalRoot target).charpoly.coeff index

/-- Cayley--Hamilton denominator for recovering a root from its square. -/
def positiveRootReconstructionDenominator
    (target : Matrix4) (coefficients : Fin 4 → Real) : Matrix4 :=
  (-coefficients 3) • target - coefficients 1 • (1 : Matrix4)

/-- Cayley--Hamilton numerator for recovering a root from its square. -/
def positiveRootReconstructionNumerator
    (target : Matrix4) (coefficients : Fin 4 → Real) : Matrix4 :=
  target * target + coefficients 2 • target +
    coefficients 0 • (1 : Matrix4)

/-- Rational Cayley--Hamilton reconstruction. -/
def positiveRootReconstruction
    (target : Matrix4) (coefficients : Fin 4 → Real) : Matrix4 :=
  (positiveRootReconstructionDenominator target coefficients)⁻¹ *
    positiveRootReconstructionNumerator target coefficients

/-- Explicit degree-four form of Cayley--Hamilton. -/
private theorem matrix4_cayleyHamilton_explicit (root : Matrix4) :
    root ^ 4 + root.charpoly.coeff 3 • root ^ 3 +
        root.charpoly.coeff 2 • root ^ 2 +
        root.charpoly.coeff 1 • root +
        root.charpoly.coeff 0 • (1 : Matrix4) = 0 := by
  have hCayley := Matrix.aeval_self_charpoly root
  rw [Polynomial.aeval_eq_sum_range' (n := 5) (by simp) root] at hCayley
  have hCoeffFour : root.charpoly.coeff 4 = 1 := by
    convert (Matrix.charpoly_monic root).coeff_natDegree using 1 <;> simp
  norm_num [Finset.sum_range_succ, hCoeffFour] at hCayley
  calc
    root ^ 4 + root.charpoly.coeff 3 • root ^ 3 +
          root.charpoly.coeff 2 • root ^ 2 +
          root.charpoly.coeff 1 • root +
          root.charpoly.coeff 0 • (1 : Matrix4) =
        root.charpoly.coeff 0 • (1 : Matrix4) +
          root.charpoly.coeff 1 • root +
          root.charpoly.coeff 2 • root ^ 2 +
          root.charpoly.coeff 3 • root ^ 3 + root ^ 4 := by abel
    _ = 0 := hCayley

/-- The reconstruction denominator times the selected root is exactly the
reconstruction numerator. -/
theorem positiveRootReconstructionDenominator_mul_root
    (target : positiveDiagonalizableLocus) :
    positiveRootReconstructionDenominator target.1
          (positiveRootCharpolyCoefficients target) *
        positiveDiagonalizableGlobalRoot target =
      positiveRootReconstructionNumerator target.1
        (positiveRootCharpolyCoefficients target) := by
  have hSquare := positiveDiagonalizableGlobalRoot_square target
  have hCayley :=
    matrix4_cayleyHamilton_explicit
      (positiveDiagonalizableGlobalRoot target)
  unfold positiveRootReconstructionDenominator
    positiveRootReconstructionNumerator positiveRootCharpolyCoefficients
  rw [show positiveDiagonalizableGlobalRoot target ^ 2 = target.1 by
      simpa [pow_two] using hSquare] at hCayley
  rw [show positiveDiagonalizableGlobalRoot target ^ 3 =
      target.1 * positiveDiagonalizableGlobalRoot target by
      rw [pow_succ, pow_two, hSquare],
    show positiveDiagonalizableGlobalRoot target ^ 4 = target.1 * target.1 by
      rw [show positiveDiagonalizableGlobalRoot target ^ 4 =
        positiveDiagonalizableGlobalRoot target ^ 2 *
          positiveDiagonalizableGlobalRoot target ^ 2 by noncomm_ring,
        show positiveDiagonalizableGlobalRoot target ^ 2 = target.1 by
          simpa [pow_two] using hSquare]] at hCayley
  let root := positiveDiagonalizableGlobalRoot target
  let matrix := target.1
  let coefficient : Fin 4 → Real := fun index => root.charpoly.coeff index
  change ((-coefficient 3) • matrix - coefficient 1 • (1 : Matrix4)) *
      root = matrix * matrix + coefficient 2 • matrix +
        coefficient 0 • (1 : Matrix4)
  simp only [sub_mul, smul_mul_assoc, one_mul]
  have hSum :
      (matrix * matrix + coefficient 2 • matrix +
          coefficient 0 • (1 : Matrix4)) +
        (coefficient 3 • (matrix * root) + coefficient 1 • root) = 0 := by
    dsimp only [root, matrix, coefficient]
    calc
      target.1 * target.1 +
            (positiveDiagonalizableGlobalRoot target).charpoly.coeff 2 • target.1 +
            (positiveDiagonalizableGlobalRoot target).charpoly.coeff 0 •
              (1 : Matrix4) +
          ((positiveDiagonalizableGlobalRoot target).charpoly.coeff 3 •
              (target.1 * positiveDiagonalizableGlobalRoot target) +
            (positiveDiagonalizableGlobalRoot target).charpoly.coeff 1 •
              positiveDiagonalizableGlobalRoot target) =
          target.1 * target.1 +
              (positiveDiagonalizableGlobalRoot target).charpoly.coeff 3 •
                (target.1 * positiveDiagonalizableGlobalRoot target) +
            (positiveDiagonalizableGlobalRoot target).charpoly.coeff 2 • target.1 +
            (positiveDiagonalizableGlobalRoot target).charpoly.coeff 1 •
              positiveDiagonalizableGlobalRoot target +
            (positiveDiagonalizableGlobalRoot target).charpoly.coeff 0 •
              (1 : Matrix4) := by abel
      _ = 0 := hCayley
  calc
    (-coefficient 3) • (matrix * root) - coefficient 1 • root =
        -(coefficient 3 • (matrix * root) + coefficient 1 • root) := by
      rw [neg_smul]
      abel
    _ = matrix * matrix + coefficient 2 • matrix +
        coefficient 0 • (1 : Matrix4) :=
      (eq_neg_of_add_eq_zero_left hSum).symm

/-- The selected root itself has the supplied positive diagonalization. -/
def positiveSimilarityRootPresentation
    (data : PositiveDiagonalizableRelativeMatrix) :
    PositiveDiagonalizableRelativeMatrix where
  target := positiveSimilarityRoot data
  eigenbasis := data.eigenbasis
  eigenbasisInv := data.eigenbasisInv
  eigenvalue := positiveSimilarityRootSpectrum data
  eigenvalue_pos := positiveSimilarityRootSpectrum_pos data
  inv_mul_basis := data.inv_mul_basis
  basis_mul_inv := data.basis_mul_inv
  target_eq := rfl

private theorem multiset_esymm_nonneg_of_nonneg
    (values : Multiset Real) (hValues : ∀ value ∈ values, 0 ≤ value)
    (degree : Nat) :
    0 ≤ values.esymm degree := by
  rw [Multiset.esymm]
  apply Multiset.sum_nonneg
  intro product hProduct
  rcases Multiset.mem_map.mp hProduct with ⟨subset, hSubset, rfl⟩
  apply Multiset.prod_nonneg
  intro value hValue
  apply hValues value
  exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp hSubset).1 hValue

theorem positiveSimilarityRoot_coeff_three_neg
    (data : PositiveDiagonalizableRelativeMatrix) :
    (positiveSimilarityRoot data).charpoly.coeff 3 < 0 := by
  let rootData := positiveSimilarityRootPresentation data
  have hRoots := positiveDiagonalizable_roots_charpoly_eq_spectrum rootData
  have hRoots' :
      (positiveSimilarityRoot data).charpoly.roots =
        Multiset.map rootData.eigenvalue Finset.univ.val := by
    simpa [rootData, positiveSimilarityRootPresentation] using hRoots
  have hCard :
      Multiset.card (positiveSimilarityRoot data).charpoly.roots =
        (positiveSimilarityRoot data).charpoly.natDegree := by
    rw [hRoots']
    simp
  have hSplits : (positiveSimilarityRoot data).charpoly.Splits :=
    Polynomial.splits_iff_card_roots.mpr hCard
  have hCoefficient := hSplits.nextCoeff_eq_neg_sum_roots_of_monic
    (Matrix.charpoly_monic (positiveSimilarityRoot data))
  have hSumPos :
      0 < (Multiset.map rootData.eigenvalue Finset.univ.val).sum := by
    change 0 < ∑ index : Fin 4, rootData.eigenvalue index
    exact Finset.sum_pos (fun index _ => rootData.eigenvalue_pos index)
      Finset.univ_nonempty
  rw [hRoots'] at hCoefficient
  calc
    (positiveSimilarityRoot data).charpoly.coeff 3 =
        (positiveSimilarityRoot data).charpoly.nextCoeff := by
      simp [Polynomial.nextCoeff, Matrix.charpoly_natDegree_eq_dim]
    _ = -(Multiset.map rootData.eigenvalue Finset.univ.val).sum := hCoefficient
    _ < 0 := neg_neg_of_pos hSumPos

theorem positiveSimilarityRoot_coeff_one_nonpos
    (data : PositiveDiagonalizableRelativeMatrix) :
    (positiveSimilarityRoot data).charpoly.coeff 1 ≤ 0 := by
  let rootData := positiveSimilarityRootPresentation data
  have hRoots := positiveDiagonalizable_roots_charpoly_eq_spectrum rootData
  have hRoots' :
      (positiveSimilarityRoot data).charpoly.roots =
        Multiset.map rootData.eigenvalue Finset.univ.val := by
    simpa [rootData, positiveSimilarityRootPresentation] using hRoots
  have hCard :
      Multiset.card (positiveSimilarityRoot data).charpoly.roots =
        (positiveSimilarityRoot data).charpoly.natDegree := by
    rw [hRoots']
    simp
  have hCoefficient := Polynomial.coeff_eq_esymm_roots_of_card hCard
    (k := 1) (by simp)
  have hEsymm :
      0 ≤ (positiveSimilarityRoot data).charpoly.roots.esymm 3 := by
    apply multiset_esymm_nonneg_of_nonneg
    intro value hValue
    rw [hRoots'] at hValue
    rcases Multiset.mem_map.mp hValue with ⟨index, _, rfl⟩
    exact (rootData.eigenvalue_pos index).le
  have hLeading :
      (positiveSimilarityRoot data).charpoly.leadingCoeff = 1 :=
    (Matrix.charpoly_monic (positiveSimilarityRoot data)).leadingCoeff
  rw [Matrix.charpoly_natDegree_eq_dim, hLeading] at hCoefficient
  norm_num at hCoefficient
  linarith

/-- Positivity of the selected spectrum makes the Cayley--Hamilton
reconstruction denominator nonsingular. -/
theorem positiveRootReconstructionDenominator_det_ne_zero
    (target : positiveDiagonalizableLocus) :
    (positiveRootReconstructionDenominator target.1
      (positiveRootCharpolyCoefficients target)).det ≠ 0 := by
  let data := chosenPositiveDiagonalization target
  let coefficient := positiveRootCharpolyCoefficients target
  have hRoot :
      positiveDiagonalizableGlobalRoot target = positiveSimilarityRoot data :=
    positiveDiagonalizableGlobalRoot_eq_of_presentation target data
      (chosenPositiveDiagonalization_target target)
  have hCoefficientThree : coefficient 3 < 0 := by
    dsimp only [coefficient, positiveRootCharpolyCoefficients]
    rw [hRoot]
    exact positiveSimilarityRoot_coeff_three_neg data
  have hCoefficientOne : coefficient 1 ≤ 0 := by
    dsimp only [coefficient, positiveRootCharpolyCoefficients]
    rw [hRoot]
    exact positiveSimilarityRoot_coeff_one_nonpos data
  let diagonalValue : Fin 4 → Real := fun index =>
    (-coefficient 3) * data.eigenvalue index - coefficient 1
  have hDiagonalValue (index : Fin 4) : 0 < diagonalValue index := by
    dsimp only [diagonalValue]
    have hProduct :
        0 < (-coefficient 3) * data.eigenvalue index :=
      mul_pos (neg_pos.mpr hCoefficientThree) (data.eigenvalue_pos index)
    linarith
  have hTarget :
      target.1 = data.eigenbasis * Matrix.diagonal data.eigenvalue *
        data.eigenbasisInv := by
    rw [← chosenPositiveDiagonalization_target target]
    exact data.target_eq
  have hDiagonal :
      Matrix.diagonal diagonalValue =
        (-coefficient 3) • Matrix.diagonal data.eigenvalue -
          coefficient 1 • (1 : Matrix4) := by
    ext first second
    by_cases hIndices : first = second
    · subst second
      simp [diagonalValue]
    · simp [diagonalValue, hIndices]
  have hDenominator :
      positiveRootReconstructionDenominator target.1 coefficient =
        data.eigenbasis * Matrix.diagonal diagonalValue *
          data.eigenbasisInv := by
    unfold positiveRootReconstructionDenominator
    rw [hTarget, hDiagonal]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      Matrix.mul_assoc, Matrix.mul_one]
    rw [data.basis_mul_inv]
  rw [show positiveRootCharpolyCoefficients target = coefficient from rfl,
    hDenominator, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (mul_ne_zero
      (Matrix.det_ne_zero_of_left_inverse data.inv_mul_basis)
      (Finset.prod_ne_zero_iff.mpr fun index _ =>
        (hDiagonalValue index).ne'))
    (Matrix.det_ne_zero_of_left_inverse data.basis_mul_inv)

/-- The global selector is exactly the rational reconstruction from its four
scalar characteristic coefficients. -/
theorem positiveRootReconstruction_eq_globalRoot
    (target : positiveDiagonalizableLocus) :
    positiveRootReconstruction target.1
        (positiveRootCharpolyCoefficients target) =
      positiveDiagonalizableGlobalRoot target := by
  unfold positiveRootReconstruction
  rw [← positiveRootReconstructionDenominator_mul_root target]
  exact Matrix.nonsing_inv_mul_cancel_left _ _
    (isUnit_iff_ne_zero.mpr
      (positiveRootReconstructionDenominator_det_ne_zero target))

end

end P0EFTJanusPositiveDiagonalizableRootCoefficientRegularity4D
end JanusFormal
