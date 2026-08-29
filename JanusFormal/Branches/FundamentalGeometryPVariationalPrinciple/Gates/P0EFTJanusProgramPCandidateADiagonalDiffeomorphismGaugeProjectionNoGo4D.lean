import Mathlib.Tactic

/-!
# Candidate-A diagonal diffeomorphism gauge-projection no-go

Candidate A currently carries two independent de Donder squares but one typed
diagonal diffeomorphism nonminimal triplet.  Already in one real component, no
single scalar-weighted projection of two independent gauge conditions can have
the sum of their squares as its square for every pair of inputs.

Thus choosing a sum, difference or scalar weighting cannot silently preserve
the existing gauge Hessian.  This elementary obstruction makes no choice of a
replacement projection or of additional field content.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateADiagonalDiffeomorphismGaugeProjectionNoGo4D

set_option autoImplicit false

/-- No single weighted scalar condition has the quadratic norm of two
independent scalar conditions on every input. -/
theorem no_singleWeightedSquare_eq_sumOfTwoSquares :
    ¬ ∃ firstWeight secondWeight : Real,
      ∀ first second : Real,
        (firstWeight * first + secondWeight * second) ^ 2 =
          first ^ 2 + second ^ 2 := by
  rintro ⟨firstWeight, secondWeight, hEquality⟩
  have hFirst : firstWeight ^ 2 = 1 := by
    simpa using hEquality 1 0
  have hSecond : secondWeight ^ 2 = 1 := by
    simpa using hEquality 0 1
  have hSum := hEquality 1 1
  have hCross : firstWeight * secondWeight = 0 := by
    nlinarith
  have hFirstNe : firstWeight ≠ 0 := by
    intro hZero
    rw [hZero] at hFirst
    norm_num at hFirst
  have hSecondZero : secondWeight = 0 :=
    (mul_eq_zero.mp hCross).resolve_left hFirstNe
  rw [hSecondZero] at hSecond
  norm_num at hSecond

end P0EFTJanusProgramPCandidateADiagonalDiffeomorphismGaugeProjectionNoGo4D
end JanusFormal
