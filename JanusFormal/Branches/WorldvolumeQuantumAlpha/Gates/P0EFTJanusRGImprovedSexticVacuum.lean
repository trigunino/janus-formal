import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusCondensateToAlphaMap

namespace JanusFormal
namespace P0EFTJanusRGImprovedSexticVacuum

set_option autoImplicit false

open P0EFTJanusCondensateToAlphaMap

/--
Algebraic data of the one-log RG-improved sextic potential

`V(v) = v^6 * (lambda6 + b * log(v/mu))`.

Rather than formalizing differentiation machinery here, the stationary
logarithmic coordinate and its exact first/second-variation coefficients are
stored in the convention obtained by direct differentiation.
-/
structure OneLogSexticVacuum where
  renormalizationScale : ℝ
  sexticCoupling : ℝ
  logCoefficient : ℝ
  logRatio : ℝ
  condensate : ℝ
  renormalizationScalePositive : 0 < renormalizationScale
  logCoefficientPositive : 0 < logCoefficient
  condensatePositive : 0 < condensate
  stationarityBracket :
    6 * sexticCoupling + logCoefficient +
      6 * logCoefficient * logRatio = 0
  condensateLaw :
    condensate = renormalizationScale * Real.exp logRatio

/-- The stationary logarithmic coordinate satisfies the exact linear equation. -/
theorem stationary_log_equation
    (s : OneLogSexticVacuum) :
    6 * s.logCoefficient * s.logRatio =
      -(6 * s.sexticCoupling + s.logCoefficient) := by
  linarith [s.stationarityBracket]

/-- The one-log truncation has at most one stationary logarithmic coordinate. -/
theorem stationary_log_ratio_unique
    (s₁ s₂ : OneLogSexticVacuum)
    (hLambda : s₁.sexticCoupling = s₂.sexticCoupling)
    (hCoefficient : s₁.logCoefficient = s₂.logCoefficient) :
    s₁.logRatio = s₂.logRatio := by
  have h₁ := s₁.stationarityBracket
  have h₂ := s₂.stationarityBracket
  rw [← hLambda, ← hCoefficient] at h₂
  have hFactor :
      6 * s₁.logCoefficient *
        (s₁.logRatio - s₂.logRatio) = 0 := by
    nlinarith [h₁, h₂]
  have hCoefficientNonzero : 6 * s₁.logCoefficient ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt s₁.logCoefficientPositive)
  have hDifference : s₁.logRatio - s₂.logRatio = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hCoefficientNonzero
  linarith

/-- Equal RG data and equal renormalization scale select the same condensate. -/
theorem stationary_condensate_unique
    (s₁ s₂ : OneLogSexticVacuum)
    (hMu : s₁.renormalizationScale = s₂.renormalizationScale)
    (hLambda : s₁.sexticCoupling = s₂.sexticCoupling)
    (hCoefficient : s₁.logCoefficient = s₂.logCoefficient) :
    s₁.condensate = s₂.condensate := by
  have hLog := stationary_log_ratio_unique s₁ s₂ hLambda hCoefficient
  calc
    s₁.condensate =
        s₁.renormalizationScale * Real.exp s₁.logRatio :=
      s₁.condensateLaw
    _ = s₂.renormalizationScale * Real.exp s₂.logRatio := by
      rw [hMu, hLog]
    _ = s₂.condensate := s₂.condensateLaw.symm

/-- Vacuum energy at the stationary point of the one-log potential. -/
def stationaryVacuumEnergy (s : OneLogSexticVacuum) : ℝ :=
  -(s.logCoefficient * s.condensate ^ 6 / 6)

/-- Radial curvature coefficient at the stationary point. -/
def stationaryRadialCurvature (s : OneLogSexticVacuum) : ℝ :=
  6 * s.logCoefficient * s.condensate ^ 4

/-- Positive logarithmic coefficient gives a negative vacuum energy. -/
theorem stationary_vacuum_energy_is_negative
    (s : OneLogSexticVacuum) :
    stationaryVacuumEnergy s < 0 := by
  unfold stationaryVacuumEnergy
  have hPower : 0 < s.condensate ^ 6 :=
    pow_pos s.condensatePositive 6
  have hProduct : 0 < s.logCoefficient * s.condensate ^ 6 / 6 :=
    div_pos (mul_pos s.logCoefficientPositive hPower) (by norm_num)
  linarith

/-- Positive logarithmic coefficient gives positive radial curvature. -/
theorem stationary_radial_curvature_is_positive
    (s : OneLogSexticVacuum) :
    0 < stationaryRadialCurvature s := by
  unfold stationaryRadialCurvature
  exact mul_pos
    (mul_pos (by norm_num) s.logCoefficientPositive)
    (pow_pos s.condensatePositive 4)

/-- First-variation coefficient in the logarithmic coordinate. -/
def logCoordinateDerivative
    (s : OneLogSexticVacuum) (x : ℝ) : ℝ :=
  s.renormalizationScale ^ 6 * Real.exp (6 * x) *
    (6 * s.sexticCoupling + s.logCoefficient +
      6 * s.logCoefficient * x)

/-- The derivative factorizes around the unique stationary logarithmic coordinate. -/
theorem derivative_factorization
    (s : OneLogSexticVacuum) (x : ℝ) :
    logCoordinateDerivative s x =
      s.renormalizationScale ^ 6 * Real.exp (6 * x) *
        (6 * s.logCoefficient * (x - s.logRatio)) := by
  unfold logCoordinateDerivative
  have hStationary := s.stationarityBracket
  congr 1
  nlinarith [hStationary]

/-- The one-log potential decreases below the stationary point. -/
theorem derivative_negative_below_vacuum
    (s : OneLogSexticVacuum) (x : ℝ)
    (hBelow : x < s.logRatio) :
    logCoordinateDerivative s x < 0 := by
  rw [derivative_factorization]
  have hScalePower : 0 < s.renormalizationScale ^ 6 :=
    pow_pos s.renormalizationScalePositive 6
  have hExp : 0 < Real.exp (6 * x) := Real.exp_pos _
  have hLinear :
      6 * s.logCoefficient * (x - s.logRatio) < 0 := by
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) s.logCoefficientPositive)
      (sub_neg.mpr hBelow)
  exact mul_neg_of_pos_of_neg (mul_pos hScalePower hExp) hLinear

/-- The one-log potential increases above the stationary point. -/
theorem derivative_positive_above_vacuum
    (s : OneLogSexticVacuum) (x : ℝ)
    (hAbove : s.logRatio < x) :
    0 < logCoordinateDerivative s x := by
  rw [derivative_factorization]
  have hScalePower : 0 < s.renormalizationScale ^ 6 :=
    pow_pos s.renormalizationScalePositive 6
  have hExp : 0 < Real.exp (6 * x) := Real.exp_pos _
  have hLinear :
      0 < 6 * s.logCoefficient * (x - s.logRatio) := by
    exact mul_pos
      (mul_pos (by norm_num) s.logCoefficientPositive)
      (sub_pos.mpr hAbove)
  exact mul_pos (mul_pos hScalePower hExp) hLinear

/--
Attach the stable one-log condensate to the already-proved primitive LL flux
map.  This closes the mathematical transport from a computed quantum vacuum to
the Janus length.
-/
structure OneLogAlphaVacuum extends OneLogSexticVacuum where
  chargePrefactor : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  chargePrefactorPositive : 0 < chargePrefactor
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  chargeFromCondensate :
    chargeUnit = chargePrefactor * condensate ^ 2
  primitiveFluxRadiusLaw :
    16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Convert to the generic condensate-to-alpha interface. -/
def asCondensateChargeAlpha
    (s : OneLogAlphaVacuum) : CondensateChargeAlpha :=
  { condensate := s.condensate
    chargePrefactor := s.chargePrefactor
    chargeUnit := s.chargeUnit
    alphaSquaredLength := s.alphaSquaredLength
    condensatePositive := s.condensatePositive
    chargePrefactorPositive := s.chargePrefactorPositive
    alphaSquaredLengthPositive := s.alphaSquaredLengthPositive
    chargeFromCondensate := s.chargeFromCondensate
    primitiveFluxRadiusLaw := s.primitiveFluxRadiusLaw }

/-- Exact stable-vacuum/LL-radius relation. -/
theorem stable_vacuum_fixes_alpha_relation
    (s : OneLogAlphaVacuum) :
    4 * s.chargePrefactor * s.condensate ^ 2 *
        s.alphaSquaredLength ^ 2 = 1 := by
  exact condensate_radius_law (asCondensateChargeAlpha s)

end P0EFTJanusRGImprovedSexticVacuum
end JanusFormal
