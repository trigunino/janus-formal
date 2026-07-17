import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRealJordanPresentationBridge4D

/-!
# Real square-root spectral obstructions in dimension four

This gate extends the positive-spectrum construction to the exact classical
real Jordan criterion.  The determinant and simple-negative-eigenvalue
obstructions, as well as the paired negative block constructions, are proved
directly.

Mathlib currently has no Jordan-chain basis or real Jordan classification.
The complete equivalence is therefore isolated as the proposition
`RealSquareRootJordanClassificationBridge4`; every consequence after that
single presentation bridge is closed locally.
-/

namespace JanusFormal
namespace P0EFTJanusRealSquareRootSpectralObstructions4D

set_option autoImplicit false

noncomputable section

open Polynomial
open P0EFTJanusPositiveRealJordanPresentationBridge4D

abbrev Matrix4 :=
  P0EFTJanusPositiveRealJordanPresentationBridge4D.Matrix4

/-- Existence of an unrestricted real matrix square root. -/
def HasRealSquareRoot (target : Matrix4) : Prop :=
  ∃ root : Matrix4, root * root = target

theorem determinant_eq_square_of_realSquareRoot
    {root target : Matrix4} (hRoot : root * root = target) :
    target.det = root.det ^ 2 := by
  rw [← hRoot, Matrix.det_mul, pow_two]

theorem determinant_nonneg_of_hasRealSquareRoot
    {target : Matrix4} (hRoot : HasRealSquareRoot target) :
    0 ≤ target.det := by
  obtain ⟨root, hRoot⟩ := hRoot
  rw [determinant_eq_square_of_realSquareRoot hRoot]
  positivity

/-- A negative determinant is an unconditional real-square-root obstruction. -/
theorem no_realSquareRoot_of_determinant_neg
    {target : Matrix4} (hDet : target.det < 0) :
    ¬ HasRealSquareRoot target := by
  intro hRoot
  exact (not_lt_of_ge (determinant_nonneg_of_hasRealSquareRoot hRoot)) hDet

/-- A diagonal matrix with a simple negative eigenvalue has no real square
root.  The proof uses only commutation of a root with its square. -/
theorem no_realSquareRoot_diagonal_of_simple_negative
    (spectrum : Fin 4 → Real) (index : Fin 4)
    (hNegative : spectrum index < 0)
    (hSimple : ∀ other, other ≠ index →
      spectrum other ≠ spectrum index) :
    ¬ HasRealSquareRoot (Matrix.diagonal spectrum) := by
  classical
  rintro ⟨root, hRoot⟩
  have hCommute :
      root * Matrix.diagonal spectrum =
        Matrix.diagonal spectrum * root := by
    calc
      root * Matrix.diagonal spectrum = root * (root * root) := by rw [hRoot]
      _ = (root * root) * root := by noncomm_ring
      _ = Matrix.diagonal spectrum * root := by rw [hRoot]
  have hRowZero : ∀ other, other ≠ index → root index other = 0 := by
    intro other hOther
    have hEntry := congrArg (fun matrix => matrix index other) hCommute
    have hEntry' :
        root index other * spectrum other =
          spectrum index * root index other := by
      simpa [Matrix.mul_apply, Matrix.diagonal_apply] using hEntry
    have hFactor :
        root index other * (spectrum other - spectrum index) = 0 := by
      nlinarith [hEntry']
    exact (mul_eq_zero.mp hFactor).resolve_right
      (sub_ne_zero.mpr (hSimple other hOther))
  have hSquareEntry :
      (∑ other : Fin 4, root index other * root other index) =
        spectrum index := by
    have hEntry := congrArg (fun matrix => matrix index index) hRoot
    simpa [Matrix.mul_apply] using hEntry
  have hCollapse :
      (∑ other : Fin 4, root index other * root other index) =
        root index index * root index index := by
    apply Finset.sum_eq_single index
    · intro other _ hOther
      rw [hRowZero other hOther]
      simp
    · simp
  rw [hCollapse] at hSquareEntry
  nlinarith [sq_nonneg (root index index)]

/-- Positive determinant is not sufficient: the two distinct simple negative
eigenvalues each violate the Jordan parity condition. -/
def positiveDeterminantNoRootWitness : Matrix4 :=
  Matrix.diagonal ![-1, -2, 1, 2]

theorem positiveDeterminantNoRootWitness_det :
    positiveDeterminantNoRootWitness.det = 4 := by
  rw [positiveDeterminantNoRootWitness, Matrix.det_diagonal,
    Fin.prod_univ_four]
  change (-1 : Real) * (-2) * 1 * 2 = 4
  norm_num

theorem positiveDeterminantNoRootWitness_noRoot :
    ¬ HasRealSquareRoot positiveDeterminantNoRootWitness := by
  unfold positiveDeterminantNoRootWitness
  apply no_realSquareRoot_diagonal_of_simple_negative
    ![-1, -2, 1, 2] (0 : Fin 4) (by norm_num)
  intro other hOther
  fin_cases other
  · exact (hOther rfl).elim
  · norm_num
  · norm_num
  · norm_num

/-- Two identical negative scalar blocks have the standard real rotation
root.  Two such pairs are displayed simultaneously in dimension four. -/
def pairedNegativeDiagonalTarget (first second : Real) : Matrix4 :=
  Matrix.diagonal ![first, first, second, second]

def pairedNegativeDiagonalRoot (first second : Real) : Matrix4 :=
  ![![0, -Real.sqrt (-first), 0, 0],
    ![Real.sqrt (-first), 0, 0, 0],
    ![0, 0, 0, -Real.sqrt (-second)],
    ![0, 0, Real.sqrt (-second), 0]]

theorem pairedNegativeDiagonalRoot_square
    (first second : Real) (hFirst : first < 0) (hSecond : second < 0) :
    pairedNegativeDiagonalRoot first second *
        pairedNegativeDiagonalRoot first second =
      pairedNegativeDiagonalTarget first second := by
  have hFirstSquare :
      Real.sqrt (-first) * Real.sqrt (-first) = -first :=
    Real.mul_self_sqrt (by linarith)
  have hSecondSquare :
      Real.sqrt (-second) * Real.sqrt (-second) = -second :=
    Real.mul_self_sqrt (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedNegativeDiagonalRoot, pairedNegativeDiagonalTarget,
      Matrix.mul_apply, Fin.sum_univ_four, hFirstSquare, hSecondSquare]

theorem pairedNegativeDiagonal_hasRealSquareRoot
    (first second : Real) (hFirst : first < 0) (hSecond : second < 0) :
    HasRealSquareRoot (pairedNegativeDiagonalTarget first second) :=
  ⟨pairedNegativeDiagonalRoot first second,
    pairedNegativeDiagonalRoot_square first second hFirst hSecond⟩

/-- Two equal Jordan blocks of size two can be paired over `Real`.  The block
matrix `[[0, B], [I, 0]]` squares to `diag(B, B)`. -/
def pairedJordan22Target (eigenvalue : Real) : Matrix4 :=
  ![![eigenvalue, 1, 0, 0],
    ![0, eigenvalue, 0, 0],
    ![0, 0, eigenvalue, 1],
    ![0, 0, 0, eigenvalue]]

def pairedJordan22Root (eigenvalue : Real) : Matrix4 :=
  ![![0, 0, eigenvalue, 1],
    ![0, 0, 0, eigenvalue],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0]]

theorem pairedJordan22Root_square (eigenvalue : Real) :
    pairedJordan22Root eigenvalue * pairedJordan22Root eigenvalue =
      pairedJordan22Target eigenvalue := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedJordan22Root, pairedJordan22Target, Matrix.mul_apply,
      Fin.sum_univ_four]

theorem pairedJordan22_hasRealSquareRoot (eigenvalue : Real) :
    HasRealSquareRoot (pairedJordan22Target eigenvalue) :=
  ⟨pairedJordan22Root eigenvalue, pairedJordan22Root_square eigenvalue⟩

/-- The shifted endomorphism used to read generalized eigenspace growth. -/
def shiftedMatrixEnd (target : Matrix4) (eigenvalue : Real) :
    Module.End Real (Fin 4 → Real) :=
  Matrix.toLin' target -
    algebraMap Real (Module.End Real (Fin 4 → Real)) eigenvalue

/-- Dimension of the kernel of `(A - λI)^power`. -/
def generalizedKernelDimension
    (target : Matrix4) (eigenvalue : Real) (power : Nat) : Nat :=
  Module.finrank Real
    (LinearMap.ker ((shiftedMatrixEnd target eigenvalue) ^ power))

/-- Exact number of Jordan blocks of a fixed size, reconstructed from the
successive generalized-kernel dimensions. -/
def jordanBlockCountAtSize4
    (target : Matrix4) (eigenvalue : Real) (size : Nat) : Nat :=
  let current := generalizedKernelDimension target eigenvalue size
  let previous := generalizedKernelDimension target eigenvalue (size - 1)
  let next := generalizedKernelDimension target eigenvalue (size + 1)
  (current - previous) - (next - current)

/-- For every negative real eigenvalue, blocks of each possible size occur in
pairs. -/
def NegativeJordanBlockParity4 (target : Matrix4) : Prop :=
  ∀ eigenvalue : Real, eigenvalue < 0 →
    Even (jordanBlockCountAtSize4 target eigenvalue 1) ∧
      Even (jordanBlockCountAtSize4 target eigenvalue 2) ∧
      Even (jordanBlockCountAtSize4 target eigenvalue 3) ∧
      Even (jordanBlockCountAtSize4 target eigenvalue 4)

/-- Dimension-four nilpotent partitions that are themselves squares.  They
are exactly unions of the partitions produced by squaring nilpotent blocks of
sizes one through four. -/
def ZeroJordanSquareAdmissible4 (target : Matrix4) : Prop :=
  let count1 := jordanBlockCountAtSize4 target 0 1
  let count2 := jordanBlockCountAtSize4 target 0 2
  let count3 := jordanBlockCountAtSize4 target 0 3
  let count4 := jordanBlockCountAtSize4 target 0 4
  count3 = 0 ∧ count4 = 0 ∧
    ((count2 = 0 ∧ count1 ≤ 4) ∨
      (count2 = 1 ∧ (count1 = 1 ∨ count1 = 2)) ∨
      (count2 = 2 ∧ count1 = 0))

/-- Exact real Jordan criterion in dimension four.  Positive real blocks and
nonreal conjugate pairs impose no further restriction. -/
def RealSquareRootJordanCriterion4 (target : Matrix4) : Prop :=
  NegativeJordanBlockParity4 target ∧ ZeroJordanSquareAdmissible4 target

/-- The single missing library-level theorem: the classical real Jordan
square-root classification, specialized to dimension four. -/
def RealSquareRootJordanClassificationBridge4 : Prop :=
  ∀ target : Matrix4,
    HasRealSquareRoot target ↔ RealSquareRootJordanCriterion4 target

theorem hasRealSquareRoot_iff_jordanCriterion
    (bridge : RealSquareRootJordanClassificationBridge4)
    (target : Matrix4) :
    HasRealSquareRoot target ↔ RealSquareRootJordanCriterion4 target :=
  bridge target

theorem hasRealSquareRoot_of_jordanCriterion
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} (hCriterion : RealSquareRootJordanCriterion4 target) :
    HasRealSquareRoot target :=
  (bridge target).2 hCriterion

theorem no_realSquareRoot_of_negativeParity_failure
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} (hFailure : ¬ NegativeJordanBlockParity4 target) :
    ¬ HasRealSquareRoot target := by
  intro hRoot
  exact hFailure ((bridge target).1 hRoot).1

theorem no_realSquareRoot_of_zeroJordan_failure
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} (hFailure : ¬ ZeroJordanSquareAdmissible4 target) :
    ¬ HasRealSquareRoot target := by
  intro hRoot
  exact hFailure ((bridge target).1 hRoot).2

end

end P0EFTJanusRealSquareRootSpectralObstructions4D
end JanusFormal
