import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableRootCoefficientRegularity4D

/-!
# Scalar spectral reduction for the positive diagonalizable root

Squaring a monic quartic with positive roots induces an explicit polynomial
map on its four nonleading coefficients.  This gate proves that map for the
global root and closes the constant root coefficient as the positive square
root of the target determinant.  The remaining regularity question is thus
finite-dimensional and scalar; no continuous eigenbasis is used.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRootScalarSpectralReduction4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology BigOperators
open Polynomial
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableRootCoefficientRegularity4D

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

/-- The four nonleading characteristic coefficients of the target. -/
def positiveTargetCharpolyCoefficients
    (target : positiveDiagonalizableLocus) : Fin 4 → Real :=
  fun index => target.1.charpoly.coeff index

private def monicQuartic (coefficient : Fin 4 → Real) : Real[X] :=
  Polynomial.X ^ 4 + Polynomial.C (coefficient 3) * Polynomial.X ^ 3 +
    Polynomial.C (coefficient 2) * Polynomial.X ^ 2 +
    Polynomial.C (coefficient 1) * Polynomial.X +
    Polynomial.C (coefficient 0)

private theorem matrix4_charpoly_eq_monicQuartic (matrix : Matrix4) :
    matrix.charpoly = monicQuartic (fun index => matrix.charpoly.coeff index) := by
  have hExpansion := (Matrix.charpoly_monic matrix).as_sum
  rw [Matrix.charpoly_natDegree_eq_dim] at hExpansion
  norm_num [Finset.sum_range_succ] at hExpansion
  calc
    matrix.charpoly =
        Polynomial.X ^ 4 +
          (Polynomial.C (matrix.charpoly.coeff 0) +
            Polynomial.C (matrix.charpoly.coeff 1) * Polynomial.X +
            Polynomial.C (matrix.charpoly.coeff 2) * Polynomial.X ^ 2 +
            Polynomial.C (matrix.charpoly.coeff 3) * Polynomial.X ^ 3) :=
      hExpansion
    _ = monicQuartic (fun index => matrix.charpoly.coeff index) := by
      unfold monicQuartic
      norm_num
      ring

private theorem monicQuartic_comp_square
    (coefficient : Fin 4 → Real) :
    (monicQuartic coefficient).comp (Polynomial.X ^ 2) =
      Polynomial.X ^ 8 +
        Polynomial.C (coefficient 3) * Polynomial.X ^ 6 +
        Polynomial.C (coefficient 2) * Polynomial.X ^ 4 +
        Polynomial.C (coefficient 1) * Polynomial.X ^ 2 +
        Polynomial.C (coefficient 0) := by
  unfold monicQuartic
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  ring

private theorem monicQuartic_mul_comp_neg
    (coefficient : Fin 4 → Real) :
    monicQuartic coefficient *
        (monicQuartic coefficient).comp (-Polynomial.X) =
      Polynomial.X ^ 8 +
        Polynomial.C (2 * coefficient 2 - coefficient 3 ^ 2) *
          Polynomial.X ^ 6 +
        Polynomial.C
            (coefficient 2 ^ 2 - 2 * coefficient 3 * coefficient 1 +
              2 * coefficient 0) * Polynomial.X ^ 4 +
        Polynomial.C (2 * coefficient 2 * coefficient 0 - coefficient 1 ^ 2) *
          Polynomial.X ^ 2 +
        Polynomial.C (coefficient 0 ^ 2) := by
  unfold monicQuartic
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The characteristic polynomial of the square, pulled back by `X ↦ X²`,
is the even product of the root characteristic polynomial. -/
theorem target_charpoly_comp_square_eq_root_even_product
    (target : positiveDiagonalizableLocus) :
    target.1.charpoly.comp (Polynomial.X ^ 2) =
      (positiveDiagonalizableGlobalRoot target).charpoly *
        (positiveDiagonalizableGlobalRoot target).charpoly.comp (-Polynomial.X) := by
  let data := chosenPositiveDiagonalization target
  let rootData := positiveSimilarityRootPresentation data
  have hTarget : target.1 = data.target :=
    (chosenPositiveDiagonalization_target target).symm
  have hRoot : positiveDiagonalizableGlobalRoot target = rootData.target := by
    simpa [rootData, positiveSimilarityRootPresentation] using
      positiveDiagonalizableGlobalRoot_eq_of_presentation target data
        (chosenPositiveDiagonalization_target target)
  rw [hTarget, hRoot,
    positiveDiagonalizable_charpoly_eq_diagonal data,
    positiveDiagonalizable_charpoly_eq_diagonal rootData,
    Matrix.charpoly_diagonal, Matrix.charpoly_diagonal]
  simp only [Polynomial.prod_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.C_comp]
  simp only [Fin.prod_univ_four]
  simp only [rootData, positiveSimilarityRootPresentation,
    positiveSimilarityRootSpectrum]
  have hSqrt (index : Fin 4) :
      Real.sqrt (data.eigenvalue index) ^ 2 = data.eigenvalue index := by
    exact Real.sq_sqrt (data.eigenvalue_pos index).le
  let squareFactor (index : Fin 4) : Real[X] :=
    Polynomial.X ^ 2 - Polynomial.C (data.eigenvalue index)
  let positiveFactor (index : Fin 4) : Real[X] :=
    Polynomial.X - Polynomial.C (Real.sqrt (data.eigenvalue index))
  let negativeFactor (index : Fin 4) : Real[X] :=
    -Polynomial.X - Polynomial.C (Real.sqrt (data.eigenvalue index))
  change squareFactor 0 * squareFactor 1 * squareFactor 2 * squareFactor 3 =
    (positiveFactor 0 * positiveFactor 1 * positiveFactor 2 * positiveFactor 3) *
      (negativeFactor 0 * negativeFactor 1 * negativeFactor 2 * negativeFactor 3)
  have hFactor (index : Fin 4) :
      positiveFactor index * negativeFactor index = -squareFactor index := by
    dsimp only [positiveFactor, negativeFactor, squareFactor]
    calc
      (Polynomial.X - Polynomial.C (Real.sqrt (data.eigenvalue index))) *
          (-Polynomial.X - Polynomial.C (Real.sqrt (data.eigenvalue index))) =
        -(Polynomial.X ^ 2 -
          Polynomial.C (Real.sqrt (data.eigenvalue index) ^ 2)) := by
            simp only [map_pow]
            ring
      _ = -(Polynomial.X ^ 2 - Polynomial.C (data.eigenvalue index)) := by
        rw [hSqrt index]
  rw [show
      (positiveFactor 0 * positiveFactor 1 * positiveFactor 2 * positiveFactor 3) *
          (negativeFactor 0 * negativeFactor 1 * negativeFactor 2 * negativeFactor 3) =
        (positiveFactor 0 * negativeFactor 0) *
          (positiveFactor 1 * negativeFactor 1) *
          (positiveFactor 2 * negativeFactor 2) *
          (positiveFactor 3 * negativeFactor 3) by ring,
    hFactor 0, hFactor 1, hFactor 2, hFactor 3]
  ring

/-- Exact scalar coefficient transformation induced by squaring the selected
positive root. -/
theorem positiveRoot_target_coefficient_relations
    (target : positiveDiagonalizableLocus) :
    positiveTargetCharpolyCoefficients target 3 =
        2 * positiveRootCharpolyCoefficients target 2 -
          positiveRootCharpolyCoefficients target 3 ^ 2 ∧
    positiveTargetCharpolyCoefficients target 2 =
        positiveRootCharpolyCoefficients target 2 ^ 2 -
          2 * positiveRootCharpolyCoefficients target 3 *
            positiveRootCharpolyCoefficients target 1 +
          2 * positiveRootCharpolyCoefficients target 0 ∧
    positiveTargetCharpolyCoefficients target 1 =
        2 * positiveRootCharpolyCoefficients target 2 *
            positiveRootCharpolyCoefficients target 0 -
          positiveRootCharpolyCoefficients target 1 ^ 2 ∧
    positiveTargetCharpolyCoefficients target 0 =
        positiveRootCharpolyCoefficients target 0 ^ 2 := by
  have hIdentity := target_charpoly_comp_square_eq_root_even_product target
  have hTargetPolynomial := matrix4_charpoly_eq_monicQuartic target.1
  have hRootPolynomial := matrix4_charpoly_eq_monicQuartic
    (positiveDiagonalizableGlobalRoot target)
  rw [hTargetPolynomial, hRootPolynomial,
    monicQuartic_comp_square, monicQuartic_mul_comp_neg] at hIdentity
  constructor
  · have hCoefficient := congrArg (fun polynomial : Real[X] => polynomial.coeff 6) hIdentity
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C] at hCoefficient
    norm_num at hCoefficient
    simpa [positiveTargetCharpolyCoefficients,
      positiveRootCharpolyCoefficients] using hCoefficient
  constructor
  · have hCoefficient := congrArg (fun polynomial : Real[X] => polynomial.coeff 4) hIdentity
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C] at hCoefficient
    norm_num at hCoefficient
    simpa [positiveTargetCharpolyCoefficients,
      positiveRootCharpolyCoefficients] using hCoefficient
  constructor
  · have hCoefficient := congrArg (fun polynomial : Real[X] => polynomial.coeff 2) hIdentity
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C] at hCoefficient
    norm_num at hCoefficient
    simpa [positiveTargetCharpolyCoefficients,
      positiveRootCharpolyCoefficients] using hCoefficient
  · have hCoefficient := congrArg (fun polynomial : Real[X] => polynomial.coeff 0) hIdentity
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow, Polynomial.coeff_C] at hCoefficient
    norm_num at hCoefficient
    simpa [positiveTargetCharpolyCoefficients,
      positiveRootCharpolyCoefficients] using hCoefficient

/-- The constant characteristic coefficient of the selected root is
strictly positive. -/
theorem positiveRootCharpolyCoefficient_zero_pos
    (target : positiveDiagonalizableLocus) :
    0 < positiveRootCharpolyCoefficients target 0 := by
  let data := chosenPositiveDiagonalization target
  have hRoot :
      positiveDiagonalizableGlobalRoot target = positiveSimilarityRoot data :=
    positiveDiagonalizableGlobalRoot_eq_of_presentation target data
      (chosenPositiveDiagonalization_target target)
  have hDetRoot :
      (positiveSimilarityRoot data).det =
        ∏ index : Fin 4, positiveSimilarityRootSpectrum data index := by
    unfold positiveSimilarityRoot positiveSimilarityDiagonalRoot
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hBasisDet : data.eigenbasis.det * data.eigenbasisInv.det = 1 := by
      rw [← Matrix.det_mul, data.basis_mul_inv, Matrix.det_one]
    calc
      data.eigenbasis.det *
            (∏ index : Fin 4, positiveSimilarityRootSpectrum data index) *
          data.eigenbasisInv.det =
        (data.eigenbasis.det * data.eigenbasisInv.det) *
          ∏ index : Fin 4, positiveSimilarityRootSpectrum data index := by ring
      _ = ∏ index : Fin 4, positiveSimilarityRootSpectrum data index := by
        rw [hBasisDet, one_mul]
  have hCoefficient :
      (positiveSimilarityRoot data).charpoly.coeff 0 =
        (positiveSimilarityRoot data).det := by
    have hDet := Matrix.det_eq_sign_charpoly_coeff
      (positiveSimilarityRoot data)
    norm_num at hDet
    exact hDet.symm
  unfold positiveRootCharpolyCoefficients
  rw [hRoot]
  change 0 < (positiveSimilarityRoot data).charpoly.coeff 0
  rw [hCoefficient, hDetRoot]
  exact Finset.prod_pos fun index _ =>
    positiveSimilarityRootSpectrum_pos data index

/-- The constant root coefficient is the positive square root of the target
constant coefficient. -/
theorem positiveRootCharpolyCoefficient_zero_eq_sqrt
    (target : positiveDiagonalizableLocus) :
    positiveRootCharpolyCoefficients target 0 =
      Real.sqrt (positiveTargetCharpolyCoefficients target 0) := by
  rw [(positiveRoot_target_coefficient_relations target).2.2.2]
  exact (Real.sqrt_sq
    (positiveRootCharpolyCoefficient_zero_pos target).le).symm

/-- The second coefficient is rationally determined by the target and the
single trace coefficient of the root. -/
theorem positiveRootCharpolyCoefficient_two_eq
    (target : positiveDiagonalizableLocus) :
    positiveRootCharpolyCoefficients target 2 =
      (positiveTargetCharpolyCoefficients target 3 +
        positiveRootCharpolyCoefficients target 3 ^ 2) / 2 := by
  linarith [(positiveRoot_target_coefficient_relations target).1]

theorem positiveRootCharpolyCoefficient_one_nonpos
    (target : positiveDiagonalizableLocus) :
    positiveRootCharpolyCoefficients target 1 ≤ 0 := by
  let data := chosenPositiveDiagonalization target
  have hRoot :
      positiveDiagonalizableGlobalRoot target = positiveSimilarityRoot data :=
    positiveDiagonalizableGlobalRoot_eq_of_presentation target data
      (chosenPositiveDiagonalization_target target)
  unfold positiveRootCharpolyCoefficients
  rw [hRoot]
  exact positiveSimilarityRoot_coeff_one_nonpos data

/-- Once coefficients zero and two are known, the sign of the positive root
selects coefficient one by an ordinary real square root. -/
theorem positiveRootCharpolyCoefficient_one_eq_neg_sqrt
    (target : positiveDiagonalizableLocus) :
    positiveRootCharpolyCoefficients target 1 =
      -Real.sqrt
        (2 * positiveRootCharpolyCoefficients target 2 *
            positiveRootCharpolyCoefficients target 0 -
          positiveTargetCharpolyCoefficients target 1) := by
  have hRelation := (positiveRoot_target_coefficient_relations target).2.2.1
  have hSquare :
      2 * positiveRootCharpolyCoefficients target 2 *
            positiveRootCharpolyCoefficients target 0 -
          positiveTargetCharpolyCoefficients target 1 =
        positiveRootCharpolyCoefficients target 1 ^ 2 := by
    linarith
  rw [hSquare, Real.sqrt_sq_eq_abs,
    abs_of_nonpos (positiveRootCharpolyCoefficient_one_nonpos target)]
  simp

private theorem positiveTargetCharpolyCoefficient_continuous_from_minors
    (degree : Nat) (hDegree : degree ≤ 4) :
    Continuous (fun target : positiveDiagonalizableLocus =>
      target.1.charpoly.coeff (4 - degree)) := by
  rw [show
      (fun target : positiveDiagonalizableLocus =>
        target.1.charpoly.coeff (4 - degree)) =
      fun target =>
        (-1 : Real) ^ degree *
          ∑ subset ∈ (Finset.univ : Finset (Fin 4)).powersetCard degree,
            (target.1.submatrix
              (Subtype.val : subset → Fin 4)
              (Subtype.val : subset → Fin 4)).det from by
        funext target
        simpa using Matrix.charpoly_coeff_eq_sum_minors
          target.1 degree hDegree]
  fun_prop

/-- Target characteristic coefficients are polynomial, hence continuous,
functions of the matrix entries. -/
theorem positiveTargetCharpolyCoefficients_continuous :
    Continuous positiveTargetCharpolyCoefficients := by
  apply continuous_pi
  intro index
  fin_cases index
  · simpa [positiveTargetCharpolyCoefficients] using
      positiveTargetCharpolyCoefficient_continuous_from_minors 4 (by norm_num)
  · simpa [positiveTargetCharpolyCoefficients] using
      positiveTargetCharpolyCoefficient_continuous_from_minors 3 (by norm_num)
  · simpa [positiveTargetCharpolyCoefficients] using
      positiveTargetCharpolyCoefficient_continuous_from_minors 2 (by norm_num)
  · simpa [positiveTargetCharpolyCoefficients] using
      positiveTargetCharpolyCoefficient_continuous_from_minors 1 (by norm_num)

theorem positiveRootCharpolyCoefficient_zero_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootCharpolyCoefficients target 0) := by
  rw [show
      (fun target : positiveDiagonalizableLocus =>
        positiveRootCharpolyCoefficients target 0) =
      fun target => Real.sqrt (positiveTargetCharpolyCoefficients target 0) from by
        funext target
        exact positiveRootCharpolyCoefficient_zero_eq_sqrt target]
  exact Real.continuous_sqrt.comp
    ((continuous_apply 0).comp positiveTargetCharpolyCoefficients_continuous)

theorem positiveRootCharpolyCoefficient_two_continuous_of_three
    (hThree : Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootCharpolyCoefficients target 3)) :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootCharpolyCoefficients target 2) := by
  rw [show
      (fun target : positiveDiagonalizableLocus =>
        positiveRootCharpolyCoefficients target 2) =
      fun target =>
        (positiveTargetCharpolyCoefficients target 3 +
          positiveRootCharpolyCoefficients target 3 ^ 2) / 2 from by
        funext target
        exact positiveRootCharpolyCoefficient_two_eq target]
  exact (((continuous_apply 3).comp
    positiveTargetCharpolyCoefficients_continuous).add (hThree.pow 2)).div_const 2

theorem positiveRootCharpolyCoefficient_one_continuous_of_three
    (hThree : Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootCharpolyCoefficients target 3)) :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootCharpolyCoefficients target 1) := by
  have hTwo := positiveRootCharpolyCoefficient_two_continuous_of_three hThree
  rw [show
      (fun target : positiveDiagonalizableLocus =>
        positiveRootCharpolyCoefficients target 1) =
      fun target =>
        -Real.sqrt
          (2 * positiveRootCharpolyCoefficients target 2 *
              positiveRootCharpolyCoefficients target 0 -
            positiveTargetCharpolyCoefficients target 1) from by
        funext target
        exact positiveRootCharpolyCoefficient_one_eq_neg_sqrt target]
  exact (Real.continuous_sqrt.comp
    (((continuous_const.mul hTwo).mul
      positiveRootCharpolyCoefficient_zero_continuous).sub
        ((continuous_apply 1).comp
          positiveTargetCharpolyCoefficients_continuous))).neg

/-- Exact final scalar frontier: all four root coefficients are continuous
if and only if the single negative-trace coefficient is continuous. -/
theorem positiveRootCharpolyCoefficients_continuous_iff_coefficient_three :
    Continuous positiveRootCharpolyCoefficients ↔
      Continuous (fun target : positiveDiagonalizableLocus =>
        positiveRootCharpolyCoefficients target 3) := by
  constructor
  · intro hCoefficients
    exact (continuous_apply 3).comp hCoefficients
  · intro hThree
    apply continuous_pi
    intro index
    fin_cases index
    · exact positiveRootCharpolyCoefficient_zero_continuous
    · exact positiveRootCharpolyCoefficient_one_continuous_of_three hThree
    · exact positiveRootCharpolyCoefficient_two_continuous_of_three hThree
    · exact hThree

/-- One real equation whose distinguished negative root is the last
remaining spectral coefficient. -/
def positiveRootTraceCoefficientEquation
    (target : positiveDiagonalizableLocus) (traceCoefficient : Real) : Real :=
  let coefficientZero :=
    Real.sqrt (positiveTargetCharpolyCoefficients target 0)
  let coefficientTwo :=
    (positiveTargetCharpolyCoefficients target 3 + traceCoefficient ^ 2) / 2
  let coefficientOne :=
    -Real.sqrt
      (2 * coefficientTwo * coefficientZero -
        positiveTargetCharpolyCoefficients target 1)
  coefficientTwo ^ 2 - 2 * traceCoefficient * coefficientOne +
    2 * coefficientZero - positiveTargetCharpolyCoefficients target 2

theorem positiveRootCharpolyCoefficient_three_neg
    (target : positiveDiagonalizableLocus) :
    positiveRootCharpolyCoefficients target 3 < 0 := by
  let data := chosenPositiveDiagonalization target
  have hRoot :
      positiveDiagonalizableGlobalRoot target = positiveSimilarityRoot data :=
    positiveDiagonalizableGlobalRoot_eq_of_presentation target data
      (chosenPositiveDiagonalization_target target)
  unfold positiveRootCharpolyCoefficients
  rw [hRoot]
  exact positiveSimilarityRoot_coeff_three_neg data

/-- The final coefficient is a negative root of the explicit scalar
equation. -/
theorem positiveRootTraceCoefficientEquation_selected_root
    (target : positiveDiagonalizableLocus) :
    positiveRootTraceCoefficientEquation target
        (positiveRootCharpolyCoefficients target 3) = 0 := by
  unfold positiveRootTraceCoefficientEquation
  rw [← positiveRootCharpolyCoefficient_zero_eq_sqrt target,
    ← positiveRootCharpolyCoefficient_two_eq target]
  dsimp only
  rw [← positiveRootCharpolyCoefficient_one_eq_neg_sqrt target]
  linarith [(positiveRoot_target_coefficient_relations target).2.1]

end

end P0EFTJanusPositiveRootScalarSpectralReduction4D
end JanusFormal
