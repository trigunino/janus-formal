import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic

/-!
# An independently supplied Lorentz metric pair with a Jordan root

This gate gives two explicit real symmetric Lorentz metrics in dimension two.
In null coordinates the plus metric is `eta = [[0,1],[1,0]]`, and the minus
metric is supplied directly, not defined by multiplying a preselected relative
matrix.  Their relative matrix is

`A(t) = I + t N`,  with  `N = [[0,1],[0,0]]` and `N^2 = 0`.

The explicit root `X(t) = I + (t/2) N` satisfies `X(t)^2 = A(t)`.  For
`t != 0`, the relative matrix is nontrivial and is proved not diagonalizable
over the reals by an explicit similarity-to-diagonal contradiction.  The
actual derivatives of both curves and their Sylvester identity are also
proved.

This is one one-parameter, two-dimensional Jordan family.  It neither defines
a principal root on the full Lorentz domain nor proves continuation across
arbitrary metric pairs.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanIndependentMetricRoot

set_option autoImplicit false

noncomputable section

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Lorentz metric in null coordinates and its explicit inverse. -/
def plusMetric : Matrix2 := !![0, 1; 1, 0]

def plusMetricInverse : Matrix2 := !![0, 1; 1, 0]

/-- Independently supplied minus metric. -/
def minusMetric (parameter : ℝ) : Matrix2 :=
  !![0, 1;
     1, parameter]

/-- Nonzero Lorentz-self-adjoint nilpotent direction. -/
def jordanNilpotent : Matrix2 := !![0, 1; 0, 0]

/-- Half of the nilpotent direction, the tangent of the root. -/
def halfJordanNilpotent : Matrix2 :=
  (1 / 2 : ℝ) • jordanNilpotent

/-- Jordan-type relative curve. -/
def jordanRelative (parameter : ℝ) : Matrix2 :=
  1 + parameter • jordanNilpotent

/-- Explicit square-root curve. -/
def jordanRoot (parameter : ℝ) : Matrix2 :=
  1 + parameter • halfJordanNilpotent

theorem plusMetric_symmetric : plusMetric.transpose = plusMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetric, Matrix.transpose_apply]

theorem minusMetric_symmetric (parameter : ℝ) :
    (minusMetric parameter).transpose = minusMetric parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusMetric, Matrix.transpose_apply]

theorem plusMetricInverse_mul_plusMetric :
    plusMetricInverse * plusMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetricInverse, plusMetric, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem plusMetric_mul_inverse :
    plusMetric * plusMetricInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetricInverse, plusMetric, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem plusMetric_det : Matrix.det plusMetric = -1 := by
  norm_num [plusMetric, Matrix.det_fin_two]

theorem minusMetric_det (parameter : ℝ) :
    Matrix.det (minusMetric parameter) = -1 := by
  rw [Matrix.det_fin_two]
  simp [minusMetric]

theorem plusMetric_nondegenerate : Matrix.det plusMetric ≠ 0 := by
  rw [plusMetric_det]
  norm_num

theorem minusMetric_nondegenerate (parameter : ℝ) :
    Matrix.det (minusMetric parameter) ≠ 0 := by
  rw [minusMetric_det]
  norm_num

/-- The relative matrix is derived from the independently displayed metrics. -/
theorem metricRelative_eq_jordanRelative (parameter : ℝ) :
    plusMetricInverse * minusMetric parameter = jordanRelative parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusMetricInverse, minusMetric, jordanRelative, jordanNilpotent,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem jordanNilpotent_ne_zero : jordanNilpotent ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix2 => matrix 0 1) hZero
  norm_num [jordanNilpotent] at hEntry

theorem jordanNilpotent_square :
    jordanNilpotent * jordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jordanNilpotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The root genuinely squares to the derived metric-relative matrix. -/
theorem jordanRoot_square (parameter : ℝ) :
    jordanRoot parameter * jordanRoot parameter = jordanRelative parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanRoot, jordanRelative, halfJordanNilpotent, jordanNilpotent,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  all_goals ring

theorem jordanRoot_square_eq_metricRelative (parameter : ℝ) :
    jordanRoot parameter * jordanRoot parameter =
      plusMetricInverse * minusMetric parameter := by
  rw [jordanRoot_square, metricRelative_eq_jordanRelative]

theorem jordanRelative_sub_one (parameter : ℝ) :
    jordanRelative parameter - 1 = parameter • jordanNilpotent := by
  simp [jordanRelative]

theorem jordanRelative_displacement_square (parameter : ℝ) :
    (jordanRelative parameter - 1) *
        (jordanRelative parameter - 1) = 0 := by
  rw [jordanRelative_sub_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanNilpotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem jordanRelative_displacement_ne_zero
    (parameter : ℝ) (hParameter : parameter ≠ 0) :
    jordanRelative parameter - 1 ≠ 0 := by
  rw [jordanRelative_sub_one]
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix2 => matrix 0 1) hZero
  have : parameter = 0 := by
    simpa [jordanNilpotent] using hEntry
  exact hParameter this

theorem jordanRelative_ne_one
    (parameter : ℝ) (hParameter : parameter ≠ 0) :
    jordanRelative parameter ≠ 1 := by
  intro hOne
  apply jordanRelative_displacement_ne_zero parameter hParameter
  rw [hOne, sub_self]

/-- Explicit real similarity-to-diagonal notion used for the Jordan audit. -/
def IsRealDiagonalizable (matrix : Matrix2) : Prop :=
  ∃ change inverse diagonal : Matrix2,
    inverse * change = 1 ∧ change * inverse = 1 ∧
      diagonal.IsDiag ∧ matrix = change * diagonal * inverse

private theorem diagonal_square_zero_implies_zero
    (diagonal : Matrix2) (hDiagonal : diagonal.IsDiag)
    (hSquare : diagonal * diagonal = 0) :
    diagonal = 0 := by
  have hZeroOne : diagonal 0 1 = 0 := hDiagonal (by decide)
  have hOneZero : diagonal 1 0 = 0 := hDiagonal (by decide)
  have hZeroZero := congrArg (fun matrix : Matrix2 => matrix 0 0) hSquare
  have hOneOne := congrArg (fun matrix : Matrix2 => matrix 1 1) hSquare
  have hDiagZero : diagonal 0 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hZeroOne, hOneZero] at hZeroZero
    nlinarith [sq_nonneg (diagonal 0 0)]
  have hDiagOne : diagonal 1 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hZeroOne, hOneZero] at hOneOne
    nlinarith [sq_nonneg (diagonal 1 1)]
  ext i j
  fin_cases i <;> fin_cases j
  · exact hDiagZero
  · exact hZeroOne
  · exact hOneZero
  · exact hDiagOne

private theorem diagonal_sub_one_eq_zero_of_square_zero
    (diagonal : Matrix2) (hDiagonal : diagonal.IsDiag)
    (hSquare : (diagonal - 1) * (diagonal - 1) = 0) :
    diagonal = 1 := by
  have hDifferenceDiagonal : (diagonal - 1).IsDiag :=
    hDiagonal.sub Matrix.isDiag_one
  have hDifferenceZero := diagonal_square_zero_implies_zero
    (diagonal - 1) hDifferenceDiagonal hSquare
  exact sub_eq_zero.mp hDifferenceZero

/-- A nontrivial member of the family is not diagonalizable over `ℝ`. -/
theorem jordanRelative_not_realDiagonalizable
    (parameter : ℝ) (hParameter : parameter ≠ 0) :
    ¬ IsRealDiagonalizable (jordanRelative parameter) := by
  rintro ⟨change, inverse, diagonal, hInverseChange, hChangeInverse,
    hDiagonal, hSimilarity⟩
  have hConjugatedDifference :
      inverse * (jordanRelative parameter - 1) * change = diagonal - 1 := by
    rw [hSimilarity]
    calc
      inverse * (change * diagonal * inverse - 1) * change =
          (inverse * change) * diagonal * (inverse * change) -
            inverse * change := by noncomm_ring
      _ = diagonal - 1 := by rw [hInverseChange]; simp
  have hDiagonalSquare :
      (diagonal - 1) * (diagonal - 1) = 0 := by
    rw [← hConjugatedDifference]
    calc
      (inverse * (jordanRelative parameter - 1) * change) *
          (inverse * (jordanRelative parameter - 1) * change) =
        inverse * (jordanRelative parameter - 1) *
          (change * inverse) * (jordanRelative parameter - 1) * change := by
            noncomm_ring
      _ = inverse *
          ((jordanRelative parameter - 1) *
            (jordanRelative parameter - 1)) * change := by
            rw [hChangeInverse]
            noncomm_ring
      _ = 0 := by rw [jordanRelative_displacement_square]; simp
  have hDiagonalOne := diagonal_sub_one_eq_zero_of_square_zero
    diagonal hDiagonal hDiagonalSquare
  apply jordanRelative_ne_one parameter hParameter
  rw [hSimilarity, hDiagonalOne, mul_one, hChangeInverse]

/-- Genuine entrywise derivative predicate for a finite matrix curve. -/
def MatrixCurveHasDerivAt
    (curve : ℝ → Matrix2) (derivative : Matrix2) (parameter : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun varied => curve varied i j)
    (derivative i j) parameter

theorem jordanRelative_hasDerivAt (parameter : ℝ) :
    MatrixCurveHasDerivAt jordanRelative jordanNilpotent parameter := by
  intro i j
  have hLogExp :=
    (Real.hasDerivAt_log (Real.exp_ne_zero parameter)).comp parameter
      (Real.hasDerivAt_exp parameter)
  have hIdRaw := hLogExp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun varied => (Real.log_exp varied).symm)
  have hId := hIdRaw
  fin_cases i <;> fin_cases j
  · simpa [jordanRelative, jordanNilpotent] using
      (hasDerivAt_const (x := parameter) (c := (1 : ℝ)))
  · simpa [jordanRelative, jordanNilpotent, Real.exp_ne_zero] using hId
  · simpa [jordanRelative, jordanNilpotent] using
      (hasDerivAt_const (x := parameter) (c := (0 : ℝ)))
  · simpa [jordanRelative, jordanNilpotent] using
      (hasDerivAt_const (x := parameter) (c := (1 : ℝ)))

theorem jordanRoot_hasDerivAt (parameter : ℝ) :
    MatrixCurveHasDerivAt jordanRoot halfJordanNilpotent parameter := by
  intro i j
  have hLogExp :=
    (Real.hasDerivAt_log (Real.exp_ne_zero parameter)).comp parameter
      (Real.hasDerivAt_exp parameter)
  have hIdRaw := hLogExp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun varied => (Real.log_exp varied).symm)
  have hId := hIdRaw
  have hHalf := hId.mul_const (1 / 2 : ℝ)
  fin_cases i <;> fin_cases j
  · simpa [jordanRoot, halfJordanNilpotent, jordanNilpotent] using
      (hasDerivAt_const (x := parameter) (c := (1 : ℝ)))
  · simpa [jordanRoot, halfJordanNilpotent, jordanNilpotent,
      Real.exp_ne_zero] using hHalf
  · simpa [jordanRoot, halfJordanNilpotent, jordanNilpotent] using
      (hasDerivAt_const (x := parameter) (c := (0 : ℝ)))
  · simpa [jordanRoot, halfJordanNilpotent, jordanNilpotent] using
      (hasDerivAt_const (x := parameter) (c := (1 : ℝ)))

theorem jordanRoot_explicit (parameter : ℝ) :
    jordanRoot parameter =
      !![1, parameter / 2;
         0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanRoot, halfJordanNilpotent, jordanNilpotent]
  all_goals ring

/-- The actual root tangent solves the differentiated square equation. -/
theorem jordanRoot_derivative_sylvester (parameter : ℝ) :
    jordanRoot parameter * halfJordanNilpotent +
        halfJordanNilpotent * jordanRoot parameter = jordanNilpotent := by
  rw [jordanRoot_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfJordanNilpotent, jordanNilpotent,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Combined certificate for the independent Lorentz pair and its nontrivial
Jordan square-root orbit. -/
theorem lorentzJordanIndependentMetricRoot_gate
    (parameter : ℝ) (hParameter : parameter ≠ 0) :
    plusMetric.transpose = plusMetric ∧
      (minusMetric parameter).transpose = minusMetric parameter ∧
      Matrix.det plusMetric = -1 ∧
      Matrix.det (minusMetric parameter) = -1 ∧
      jordanRoot parameter * jordanRoot parameter =
        plusMetricInverse * minusMetric parameter ∧
      jordanRelative parameter ≠ 1 ∧
      (jordanRelative parameter - 1) *
        (jordanRelative parameter - 1) = 0 ∧
      jordanRelative parameter - 1 ≠ 0 ∧
      ¬ IsRealDiagonalizable (jordanRelative parameter) ∧
      MatrixCurveHasDerivAt jordanRoot halfJordanNilpotent parameter ∧
      MatrixCurveHasDerivAt jordanRelative jordanNilpotent parameter ∧
      jordanRoot parameter * halfJordanNilpotent +
          halfJordanNilpotent * jordanRoot parameter = jordanNilpotent := by
  exact ⟨plusMetric_symmetric, minusMetric_symmetric parameter,
    plusMetric_det, minusMetric_det parameter,
    jordanRoot_square_eq_metricRelative parameter,
    jordanRelative_ne_one parameter hParameter,
    jordanRelative_displacement_square parameter,
    jordanRelative_displacement_ne_zero parameter hParameter,
    jordanRelative_not_realDiagonalizable parameter hParameter,
    jordanRoot_hasDerivAt parameter, jordanRelative_hasDerivAt parameter,
    jordanRoot_derivative_sylvester parameter⟩

end

end P0EFTJanusLorentzJordanIndependentMetricRoot
end JanusFormal
