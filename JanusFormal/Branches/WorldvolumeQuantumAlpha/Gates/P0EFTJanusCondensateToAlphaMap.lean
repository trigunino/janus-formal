import Mathlib

namespace JanusFormal
namespace P0EFTJanusCondensateToAlphaMap

set_option autoImplicit false

/-- Quantum condensate normalization of the LL auxiliary charge. -/
structure CondensateChargeAlpha where
  condensate : ℝ
  chargePrefactor : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  condensatePositive : 0 < condensate
  chargePrefactorPositive : 0 < chargePrefactor
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  chargeFromCondensate :
    chargeUnit = chargePrefactor * condensate ^ 2
  primitiveFluxRadiusLaw :
    16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- The positive primitive branch gives the unsquared condensate-radius law. -/
theorem condensate_radius_law
    (s : CondensateChargeAlpha) :
    4 * s.chargePrefactor * s.condensate ^ 2 *
        s.alphaSquaredLength ^ 2 = 1 := by
  have hChargePositive : 0 < s.chargeUnit := by
    rw [s.chargeFromCondensate]
    positivity
  let x : ℝ :=
    4 * s.chargeUnit * s.alphaSquaredLength ^ 2
  have hSquare : x ^ 2 = 1 := by
    dsimp [x]
    calc
      (4 * s.chargeUnit * s.alphaSquaredLength ^ 2) ^ 2 =
          16 * s.chargeUnit ^ 2 * s.alphaSquaredLength ^ 4 := by ring
      _ = 1 := s.primitiveFluxRadiusLaw
  have hPositive : 0 < x := by
    dsimp [x]
    positivity
  have hFactor : (x - 1) * (x + 1) = 0 := by
    nlinarith [hSquare]
  have hx : x = 1 := by
    rcases mul_eq_zero.mp hFactor with hMinus | hPlus
    · linarith
    · have hSumPositive : 0 < x + 1 := by linarith
      exact False.elim ((ne_of_gt hSumPositive) hPlus)
  dsimp [x] at hx
  rw [s.chargeFromCondensate] at hx
  nlinarith

/-- Unit prefactor gives `2*v*A = 1`. -/
theorem unit_prefactor_condensate_alpha_law
    (s : CondensateChargeAlpha)
    (hUnit : s.chargePrefactor = 1) :
    2 * s.condensate * s.alphaSquaredLength = 1 := by
  have hSquared := condensate_radius_law s
  rw [hUnit] at hSquared
  let y : ℝ := 2 * s.condensate * s.alphaSquaredLength
  have hySquare : y ^ 2 = 1 := by
    dsimp [y]
    nlinarith [hSquared]
  have hyPositive : 0 < y := by
    dsimp [y]
    positivity
  have hFactor : (y - 1) * (y + 1) = 0 := by
    nlinarith [hySquare]
  rcases mul_eq_zero.mp hFactor with hMinus | hPlus
  · dsimp [y] at hMinus ⊢
    linarith
  · have hSumPositive : 0 < y + 1 := by linarith
    exact False.elim ((ne_of_gt hSumPositive) hPlus)

/--
The remaining prediction problem is now concentrated in the unique stable value
of the renormalized condensate and the dimensionless prefactor.
-/
structure CondensateMapStatus where
  compositeOperatorRenormalized : Prop
  condensateGaugeIndependent : Prop
  condensateSchemeIndependent : Prop
  chargePrefactorComputed : Prop
  primitiveFluxLawDerived : Prop
  uniqueStableCondensateSelected : Prop
  alphaMapClosed : Prop


def condensateMapClosed (s : CondensateMapStatus) : Prop :=
  s.compositeOperatorRenormalized /\
  s.condensateGaugeIndependent /\
  s.condensateSchemeIndependent /\
  s.chargePrefactorComputed /\
  s.primitiveFluxLawDerived /\
  s.uniqueStableCondensateSelected /\
  s.alphaMapClosed

end P0EFTJanusCondensateToAlphaMap
end JanusFormal
