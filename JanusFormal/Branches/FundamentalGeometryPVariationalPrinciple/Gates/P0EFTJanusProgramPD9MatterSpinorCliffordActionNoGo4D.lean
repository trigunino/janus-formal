import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D

/-!
# Obstruction to a rank-two D9 Clifford action

After removal of its nonzero scalar `U(1)` phase, the one-loop D9 matter
transition is `ambientHalfGammaGenerator`.  Since the throat deck map has
identity tangent monodromy, every descended Clifford generator would commute
with this matrix.  Its centralizer in `M₂(ℂ)` is commutative, which is
incompatible with two invertible anticommuting Clifford generators.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorCliffordActionNoGo4D

set_option autoImplicit false
noncomputable section

open scoped Matrix
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D

@[simp] theorem normalizedD9MatterSpinorDeckGenerator :
    (ambientHalfGammaZ4Representation 1 : AmbientComplexMatrix2) =
      ambientHalfGammaGenerator := by
  rw [ambientHalfGammaZ4Representation_one]
  rfl

private theorem centralizer_generator_entries
    (matrix : AmbientComplexMatrix2)
    (hMatrix : matrix * ambientHalfGammaGenerator =
      ambientHalfGammaGenerator * matrix) :
    matrix 1 1 = matrix 0 0 ∧ matrix 1 0 = -matrix 0 1 := by
  constructor
  · have hEntry := congrArg (fun value => value 0 1) hMatrix
    simpa [ambientHalfGammaGenerator, Matrix.mul_apply,
      Fin.sum_univ_succ] using hEntry.symm
  · have hEntry := congrArg (fun value => value 0 0) hMatrix
    simpa [ambientHalfGammaGenerator, Matrix.mul_apply,
      Fin.sum_univ_succ] using hEntry.symm

theorem centralizer_ambientHalfGammaGenerator_commutative
    (first second : AmbientComplexMatrix2)
    (hFirst : first * ambientHalfGammaGenerator =
      ambientHalfGammaGenerator * first)
    (hSecond : second * ambientHalfGammaGenerator =
      ambientHalfGammaGenerator * second) :
    first * second = second * first := by
  obtain ⟨hFirstDiag, hFirstOff⟩ :=
    centralizer_generator_entries first hFirst
  obtain ⟨hSecondDiag, hSecondOff⟩ :=
    centralizer_generator_entries second hSecond
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    simp only [hFirstDiag, hFirstOff, hSecondDiag, hSecondOff]
  all_goals ring

/-- The algebraic data required from a rank-two negative Clifford frame after
normalizing away the scalar quarter-root phase of the deck transition. -/
structure D9MatterSpinorDeckCompatibleCliffordFrame where
  gamma : Fin 3 → AmbientComplexMatrix2
  square : ∀ index, gamma index * gamma index =
    -(1 : AmbientComplexMatrix2)
  anticommute : ∀ first second, first ≠ second →
    gamma first * gamma second = -(gamma second * gamma first)
  deckCompatible : ∀ index,
    gamma index * ambientHalfGammaGenerator =
      ambientHalfGammaGenerator * gamma index

theorem d9MatterSpinorDeckCompatibleCliffordFrame_false
    (frame : D9MatterSpinorDeckCompatibleCliffordFrame) : False := by
  let first := frame.gamma 0
  let second := frame.gamma 1
  have hComm : first * second = second * first :=
    centralizer_ambientHalfGammaGenerator_commutative first second
      (frame.deckCompatible 0) (frame.deckCompatible 1)
  have hAnti : first * second = -(second * first) :=
    frame.anticommute 0 1 (by decide)
  rw [← hComm] at hAnti
  have hProductZero : first * second = 0 := by
    ext row column
    have hEntry := congrArg (fun value => value row column) hAnti
    simp only [Matrix.neg_apply] at hEntry
    have hTwo : (2 : Complex) * (first * second) row column = 0 := by
      calc
        (2 : Complex) * (first * second) row column =
            (first * second) row column + (first * second) row column := by ring
        _ = 0 := by nth_rewrite 1 [hEntry]; simp
    rcases mul_eq_zero.mp hTwo with hTwoZero | hValue
    · norm_num at hTwoZero
    · exact hValue
  have hSecondZero : second = 0 := by
    calc
      second = -(first * first) * second := by
        rw [frame.square 0]
        simp
      _ = -first * (first * second) := by
        simp only [neg_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hProductZero, mul_zero]
  have hSquare := frame.square 1
  change second * second = -(1 : AmbientComplexMatrix2) at hSquare
  rw [hSecondZero, zero_mul] at hSquare
  have hEntry := congrArg (fun value => value 0 0) hSquare
  simpa using hEntry

theorem no_d9MatterSpinorDeckCompatibleCliffordFrame :
    ¬ Nonempty D9MatterSpinorDeckCompatibleCliffordFrame := by
  rintro ⟨frame⟩
  exact d9MatterSpinorDeckCompatibleCliffordFrame_false frame

end
end P0EFTJanusProgramPD9MatterSpinorCliffordActionNoGo4D
end JanusFormal
