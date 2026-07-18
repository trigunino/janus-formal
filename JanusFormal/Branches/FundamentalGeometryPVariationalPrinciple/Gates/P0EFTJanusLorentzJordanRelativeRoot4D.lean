import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableRelativeRoot4D
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic

/-!
# A genuine four-dimensional Lorentz Jordan root

This gate embeds the null-coordinate Lorentz Jordan family into dimension
four with two additional positive spatial directions.  The two symmetric
metrics are supplied independently; their relative matrix has a nontrivial
size-two Jordan block, and the displayed real root squares exactly to it.
For nonzero parameter the relative matrix is proved not real diagonalizable.

This is one admissible 4D Jordan stratum, not a classification of all Jordan
types or a global continuation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanRelativeRoot4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusPositiveDiagonalizableRelativeRoot4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

/-- Standard Lorentz metric in null coordinates, with two positive spatial
directions. -/
def plusMetric4 : Matrix4 :=
  ![![0, 1, 0, 0],
    ![1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

def plusMetricInverse4 : Matrix4 := plusMetric4

/-- Independently supplied second Lorentz metric. -/
def minusMetric4 (parameter : Real) : Matrix4 :=
  ![![0, 1, 0, 0],
    ![1, parameter, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

def jordanNilpotent4 : Matrix4 :=
  ![![0, 1, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

def jordanRelative4 (parameter : Real) : Matrix4 :=
  1 + parameter • jordanNilpotent4

def jordanRoot4 (parameter : Real) : Matrix4 :=
  1 + (parameter / 2) • jordanNilpotent4

theorem plusMetric4_symmetric : plusMetric4.transpose = plusMetric4 := by
  ext first second
  fin_cases first <;> fin_cases second <;> rfl

theorem minusMetric4_symmetric (parameter : Real) :
    (minusMetric4 parameter).transpose = minusMetric4 parameter := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [minusMetric4, Matrix.transpose_apply]

theorem plusMetricInverse4_mul_plusMetric4 :
    plusMetricInverse4 * plusMetric4 = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [plusMetricInverse4, plusMetric4, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem plusMetric4_mul_inverse :
    plusMetric4 * plusMetricInverse4 = 1 := by
  simpa [plusMetricInverse4] using plusMetricInverse4_mul_plusMetric4

/-- The Jordan target is derived from the two independently supplied metrics. -/
theorem metricRelative4_eq_jordanRelative4 (parameter : Real) :
    plusMetricInverse4 * minusMetric4 parameter =
      jordanRelative4 parameter := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [plusMetricInverse4, plusMetric4, minusMetric4, jordanRelative4,
      jordanNilpotent4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jordanNilpotent4_ne_zero : jordanNilpotent4 ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 1) hZero
  norm_num [jordanNilpotent4] at hEntry

theorem jordanNilpotent4_square :
    jordanNilpotent4 * jordanNilpotent4 = 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [jordanNilpotent4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jordanRoot4_square (parameter : Real) :
    jordanRoot4 parameter * jordanRoot4 parameter =
      jordanRelative4 parameter := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [jordanRoot4, jordanRelative4, jordanNilpotent4,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem jordanRoot4_square_eq_metricRelative4 (parameter : Real) :
    jordanRoot4 parameter * jordanRoot4 parameter =
      plusMetricInverse4 * minusMetric4 parameter := by
  rw [jordanRoot4_square, metricRelative4_eq_jordanRelative4]

theorem jordanRelative4_sub_one (parameter : Real) :
    jordanRelative4 parameter - 1 = parameter • jordanNilpotent4 := by
  simp [jordanRelative4]

theorem jordanRelative4_displacement_square (parameter : Real) :
    (jordanRelative4 parameter - 1) *
        (jordanRelative4 parameter - 1) = 0 := by
  rw [jordanRelative4_sub_one]
  simp [jordanNilpotent4_square]

theorem jordanRelative4_ne_one
    (parameter : Real) (hParameter : parameter ≠ 0) :
    jordanRelative4 parameter ≠ 1 := by
  intro hOne
  have hEntry := congrArg
    (fun matrix : Matrix4 => matrix 0 1) hOne
  simp [jordanRelative4, jordanNilpotent4] at hEntry
  exact hParameter hEntry

/-- Explicit similarity-to-diagonal notion for the 4D Jordan audit. -/
def IsRealDiagonalizable4 (matrix : Matrix4) : Prop :=
  ∃ change inverse diagonal : Matrix4,
    inverse * change = 1 ∧ change * inverse = 1 ∧
      diagonal.IsDiag ∧ matrix = change * diagonal * inverse

private theorem diagonal4_square_zero_implies_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hSquare : diagonal * diagonal = 0) :
    diagonal = 0 := by
  have hSquareDiag :
      Matrix.diagonal (Matrix.diag diagonal) *
          Matrix.diagonal (Matrix.diag diagonal) = 0 := by
    rw [hDiagonal.diagonal_diag]
    exact hSquare
  rw [← hDiagonal.diagonal_diag]
  ext first second
  by_cases hIndices : first = second
  · subst second
    have hEntry := congrArg
      (fun matrix : Matrix4 => matrix first first) hSquareDiag
    simp at hEntry
    simpa using hEntry
  · simp [hIndices]

private theorem diagonal4_sub_one_eq_zero_of_square_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hSquare : (diagonal - 1) * (diagonal - 1) = 0) :
    diagonal = 1 := by
  have hDifferenceDiagonal : (diagonal - 1).IsDiag :=
    hDiagonal.sub Matrix.isDiag_one
  have hDifferenceZero := diagonal4_square_zero_implies_zero
    (diagonal - 1) hDifferenceDiagonal hSquare
  exact sub_eq_zero.mp hDifferenceZero

/-- Every nontrivial member has an actual Jordan obstruction to real
diagonalization. -/
theorem jordanRelative4_not_realDiagonalizable
    (parameter : Real) (hParameter : parameter ≠ 0) :
    ¬ IsRealDiagonalizable4 (jordanRelative4 parameter) := by
  rintro ⟨change, inverse, diagonal, hInverseChange, hChangeInverse,
    hDiagonal, hSimilarity⟩
  have hConjugatedDifference :
      inverse * (jordanRelative4 parameter - 1) * change = diagonal - 1 := by
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
      (inverse * (jordanRelative4 parameter - 1) * change) *
          (inverse * (jordanRelative4 parameter - 1) * change) =
        inverse * (jordanRelative4 parameter - 1) *
          (change * inverse) * (jordanRelative4 parameter - 1) * change := by
            noncomm_ring
      _ = inverse *
          ((jordanRelative4 parameter - 1) *
            (jordanRelative4 parameter - 1)) * change := by
            rw [hChangeInverse]
            noncomm_ring
      _ = 0 := by rw [jordanRelative4_displacement_square]; simp
  have hDiagonalOne := diagonal4_sub_one_eq_zero_of_square_zero
    diagonal hDiagonal hDiagonalSquare
  apply jordanRelative4_ne_one parameter hParameter
  rw [hSimilarity, hDiagonalOne, mul_one, hChangeInverse]

theorem lorentz_jordan_relative_root4D_closure
    (parameter : Real) (hParameter : parameter ≠ 0) :
    plusMetric4.transpose = plusMetric4 ∧
      (minusMetric4 parameter).transpose = minusMetric4 parameter ∧
      jordanRoot4 parameter * jordanRoot4 parameter =
        plusMetricInverse4 * minusMetric4 parameter ∧
      ¬ IsRealDiagonalizable4 (jordanRelative4 parameter) :=
  ⟨plusMetric4_symmetric, minusMetric4_symmetric parameter,
    jordanRoot4_square_eq_metricRelative4 parameter,
    jordanRelative4_not_realDiagonalizable parameter hParameter⟩

end

end P0EFTJanusLorentzJordanRelativeRoot4D
end JanusFormal
