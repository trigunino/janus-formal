import Mathlib

namespace JanusFormal
namespace P0EFTJanusCondensateToAlphaMap

set_option autoImplicit false

/--
Dimensionally consistent quantum normalization of the LL auxiliary charge.

`condensateMass` denotes the positive composite scale
`σ = φ†φ/N`, which has mass dimension one in `2+1` dimensions.
`chargeAmplitude` is dimensionless and

`q_LL = chargeAmplitude^2 * σ^2`

has mass dimension two, as required by
`16*q_LL^2*A^4 = 1` when `A` is a length.
-/
structure CondensateChargeAlpha where
  condensateMass : ℝ
  chargeAmplitude : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  condensateMassPositive : 0 < condensateMass
  chargeAmplitudePositive : 0 < chargeAmplitude
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  chargeFromCondensate :
    chargeUnit = chargeAmplitude ^ 2 * condensateMass ^ 2
  primitiveFluxRadiusLaw :
    16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- The primitive flux law first gives the positive relation `4*q*A^2 = 1`. -/
theorem positive_charge_radius_law
    (s : CondensateChargeAlpha) :
    4 * s.chargeUnit * s.alphaSquaredLength ^ 2 = 1 := by
  have hCondensateSquare : 0 < s.condensateMass ^ 2 :=
    pow_pos s.condensateMassPositive 2
  have hAmplitudeSquare : 0 < s.chargeAmplitude ^ 2 :=
    pow_pos s.chargeAmplitudePositive 2
  have hChargePositive : 0 < s.chargeUnit := by
    rw [s.chargeFromCondensate]
    exact mul_pos hAmplitudeSquare hCondensateSquare
  have hAlphaSquare : 0 < s.alphaSquaredLength ^ 2 :=
    pow_pos s.alphaSquaredLengthPositive 2
  let x : ℝ := 4 * s.chargeUnit * s.alphaSquaredLength ^ 2
  have hSquare : x ^ 2 = 1 := by
    dsimp [x]
    calc
      (4 * s.chargeUnit * s.alphaSquaredLength ^ 2) ^ 2 =
          16 * s.chargeUnit ^ 2 * s.alphaSquaredLength ^ 4 := by ring
      _ = 1 := s.primitiveFluxRadiusLaw
  have hPositive : 0 < x := by
    dsimp [x]
    exact mul_pos (mul_pos (by norm_num) hChargePositive) hAlphaSquare
  have hFactor : (x - 1) * (x + 1) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hFactor with hMinus | hPlus
  · dsimp [x] at hMinus ⊢
    linarith
  · have hSumPositive : 0 < x + 1 := by linarith
    exact False.elim ((ne_of_gt hSumPositive) hPlus)

/--
The exact dimensionally consistent condensate/length law is
`2*chargeAmplitude*σ*A = 1`.
-/
theorem condensate_alpha_law
    (s : CondensateChargeAlpha) :
    2 * s.chargeAmplitude * s.condensateMass *
        s.alphaSquaredLength = 1 := by
  have hChargeRadius := positive_charge_radius_law s
  rw [s.chargeFromCondensate] at hChargeRadius
  let y : ℝ :=
    2 * s.chargeAmplitude * s.condensateMass *
      s.alphaSquaredLength
  have hSquare : y ^ 2 = 1 := by
    dsimp [y]
    calc
      (2 * s.chargeAmplitude * s.condensateMass *
          s.alphaSquaredLength) ^ 2 =
        4 * (s.chargeAmplitude ^ 2 * s.condensateMass ^ 2) *
          s.alphaSquaredLength ^ 2 := by ring
      _ = 1 := hChargeRadius
  have hPositive : 0 < y := by
    dsimp [y]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) s.chargeAmplitudePositive)
        s.condensateMassPositive)
      s.alphaSquaredLengthPositive
  have hFactor : (y - 1) * (y + 1) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hFactor with hMinus | hPlus
  · dsimp [y] at hMinus ⊢
    linarith
  · have hSumPositive : 0 < y + 1 := by linarith
    exact False.elim ((ne_of_gt hSumPositive) hPlus)

/-- Unit amplitude gives `2*σ*A = 1`. -/
theorem unit_amplitude_condensate_alpha_law
    (s : CondensateChargeAlpha)
    (hUnit : s.chargeAmplitude = 1) :
    2 * s.condensateMass * s.alphaSquaredLength = 1 := by
  have hLaw := condensate_alpha_law s
  rw [hUnit] at hLaw
  norm_num at hLaw ⊢
  exact hLaw

/--
The remaining prediction problem is concentrated in the unique stable value of
`σ` and the dimensionless charge amplitude.
-/
structure CondensateMapStatus where
  compositeOperatorRenormalized : Prop
  condensateGaugeIndependent : Prop
  condensateSchemeIndependent : Prop
  chargeAmplitudeComputed : Prop
  primitiveFluxLawDerived : Prop
  uniqueStableCondensateSelected : Prop
  alphaMapClosed : Prop


def condensateMapClosed (s : CondensateMapStatus) : Prop :=
  s.compositeOperatorRenormalized /\
  s.condensateGaugeIndependent /\
  s.condensateSchemeIndependent /\
  s.chargeAmplitudeComputed /\
  s.primitiveFluxLawDerived /\
  s.uniqueStableCondensateSelected /\
  s.alphaMapClosed

end P0EFTJanusCondensateToAlphaMap
end JanusFormal
