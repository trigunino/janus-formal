import Mathlib

/-!
# From quadratic Gårding to an operator lower bound

The finite-sector argument naturally produces a quadratic estimate.  H12 uses a
norm lower bound for the displayed operator.  Cauchy--Schwarz is isolated here
as an upper bound on the quadratic energy, giving

`c ‖x‖² ≤ energy(x) ≤ ‖x‖ ‖H x‖`

and hence `c ‖x‖ ≤ ‖H x‖`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D

set_option autoImplicit false
noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A quadratic Gårding estimate paired with the Cauchy--Schwarz upper bound for
one bounded operator. -/
structure QuadraticGardingOperatorData
    (operator : E →L[Real] E) where
  margin : Real
  margin_pos : 0 < margin
  energy : E → Real
  energy_lower : ∀ vector,
    margin * ‖vector‖ ^ 2 ≤ energy vector
  energy_upper : ∀ vector,
    energy vector ≤ ‖vector‖ * ‖operator vector‖

namespace QuadraticGardingOperatorData

/-- The quadratic estimate implies the operator norm lower bound. -/
theorem lowerBound
    {operator : E →L[Real] E}
    (data : QuadraticGardingOperatorData operator)
    (vector : E) :
    data.margin * ‖vector‖ ≤ ‖operator vector‖ := by
  by_cases hVector : vector = 0
  · subst hVector
    simp
  · have hNorm : 0 < ‖vector‖ := norm_pos_iff.mpr hVector
    have hLower := data.energy_lower vector
    have hUpper := data.energy_upper vector
    nlinarith

/-- A positive operator lower bound gives injectivity. -/
theorem injective
    {operator : E →L[Real] E}
    (data : QuadraticGardingOperatorData operator) :
    Function.Injective operator := by
  intro first second hEqual
  have hDifference : operator (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := data.lowerBound (first - second)
  rw [hDifference, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    by_contra hNonzero
    have hNormPos : 0 < ‖first - second‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNonzero)
    have hProductPos :
        0 < data.margin * ‖first - second‖ :=
      mul_pos data.margin_pos hNormPos
    exact (not_lt_of_ge hBound) hProductPos
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Public bridge from quadratic Gårding to H12-style operator control. -/
theorem quadratic_garding_operator_lower_bound_gate
    (operator : E →L[Real] E)
    (data : QuadraticGardingOperatorData operator) :
    (∀ vector, data.margin * ‖vector‖ ≤ ‖operator vector‖) ∧
      Function.Injective operator :=
  ⟨data.lowerBound, data.injective⟩

end QuadraticGardingOperatorData

end
end P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D
end JanusFormal
