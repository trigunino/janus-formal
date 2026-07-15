import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwoSheetActionNoGo

set_option autoImplicit false

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- First variation restricted to the M15 tangent relation
`variationMinus = -variationPlus`. -/
def constrainedFirstVariation
    (equationPlus equationMinus : V →ₗ[ℝ] ℝ)
    (variation : V) : ℝ :=
  equationPlus variation + equationMinus (-variation)

/-- A sign-linked variation sees only the difference of the two Euler
functionals.  It does not force either functional to vanish separately. -/
theorem constrained_stationarity_iff_equations_equal
    (equationPlus equationMinus : V →ₗ[ℝ] ℝ) :
    (∀ variation, constrainedFirstVariation equationPlus equationMinus
        variation = 0) ↔
      equationPlus = equationMinus := by
  constructor
  · intro hStationary
    ext variation
    have h := hStationary variation
    simp [constrainedFirstVariation] at h
    linarith
  · intro hEqual variation
    rw [hEqual]
    simp [constrainedFirstVariation]

/-- Equal nonzero Euler functionals are stationary under the linked variation,
which gives a direct counterexample to splitting the constrained stationarity
condition into two field equations. -/
theorem equal_nonzero_equations_are_constrained_stationary
    (equation : V →ₗ[ℝ] ℝ)
    (hNonzero : equation ≠ 0) :
    (∀ variation, constrainedFirstVariation equation equation variation = 0) ∧
      equation ≠ 0 ∧ equation ≠ 0 := by
  exact ⟨(constrained_stationarity_iff_equations_equal equation equation).2 rfl,
    hNonzero, hNonzero⟩

/-- Minimal exchange-symmetric local interaction in a two-mode reduction. -/
def exchangeSymmetricInteraction (coupling x y : ℝ) : ℝ :=
  coupling * (x - y) ^ 2

theorem exchangeSymmetricInteraction_exchange
    (coupling x y : ℝ) :
    exchangeSymmetricInteraction coupling x y =
      exchangeSymmetricInteraction coupling y x := by
  unfold exchangeSymmetricInteraction
  have hSquare : (x - y) ^ 2 = (y - x) ^ 2 := by
    ring
  exact congrArg (fun value : ℝ => coupling * value) hSquare

/-- Exchange symmetry and locality alone leave at least a one-parameter family
of distinct interactions, so they cannot select a unique two-sheet action. -/
theorem exchange_symmetry_does_not_select_unique_interaction
    (firstCoupling secondCoupling : ℝ)
    (hDistinct : firstCoupling ≠ secondCoupling) :
    (∀ x y,
      exchangeSymmetricInteraction firstCoupling x y =
        exchangeSymmetricInteraction firstCoupling y x) ∧
    (∀ x y,
      exchangeSymmetricInteraction secondCoupling x y =
        exchangeSymmetricInteraction secondCoupling y x) ∧
    exchangeSymmetricInteraction firstCoupling ≠
      exchangeSymmetricInteraction secondCoupling := by
  refine ⟨exchangeSymmetricInteraction_exchange firstCoupling,
    exchangeSymmetricInteraction_exchange secondCoupling, ?_⟩
  intro hEqual
  have hAtPoint := congrFun (congrFun hEqual 1) 0
  simp [exchangeSymmetricInteraction] at hAtPoint
  exact hDistinct hAtPoint

end P0EFTJanusTwoSheetActionNoGo
end JanusFormal
