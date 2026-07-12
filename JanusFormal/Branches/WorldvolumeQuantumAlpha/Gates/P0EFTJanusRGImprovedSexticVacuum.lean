import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusCondensateToAlphaMap

namespace JanusFormal
namespace P0EFTJanusRGImprovedSexticVacuum

set_option autoImplicit false

open P0EFTJanusCondensateToAlphaMap

/--
Algebraic data for the RG-improved composite potential

`V(σ) = σ^3 * (lambda6 + b * log(σ/mu))`.

The gauge-invariant composite `σ = φ†φ/N` has mass dimension one, so the
potential has the required dimension three in `2+1` dimensions.
-/
structure OneLogCompositeVacuum where
  renormalizationMass : ℝ
  sexticCoupling : ℝ
  logCoefficient : ℝ
  logRatio : ℝ
  condensateMass : ℝ
  renormalizationMassPositive : 0 < renormalizationMass
  logCoefficientPositive : 0 < logCoefficient
  condensateMassPositive : 0 < condensateMass
  stationarityBracket :
    3 * sexticCoupling + logCoefficient +
      3 * logCoefficient * logRatio = 0
  condensateLaw :
    condensateMass = renormalizationMass * Real.exp logRatio

/-- Exact stationary logarithmic equation. -/
theorem stationary_log_equation
    (s : OneLogCompositeVacuum) :
    3 * s.logCoefficient * s.logRatio =
      -(3 * s.sexticCoupling + s.logCoefficient) := by
  linarith [s.stationarityBracket]

/-- The one-log approximation has at most one stationary logarithmic coordinate. -/
theorem stationary_log_ratio_unique
    (s₁ s₂ : OneLogCompositeVacuum)
    (hLambda : s₁.sexticCoupling = s₂.sexticCoupling)
    (hCoefficient : s₁.logCoefficient = s₂.logCoefficient) :
    s₁.logRatio = s₂.logRatio := by
  have h₁ := s₁.stationarityBracket
  have h₂ := s₂.stationarityBracket
  rw [← hLambda, ← hCoefficient] at h₂
  have hFactor :
      3 * s₁.logCoefficient *
        (s₁.logRatio - s₂.logRatio) = 0 := by
    nlinarith [h₁, h₂]
  have hCoefficientNonzero : 3 * s₁.logCoefficient ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt s₁.logCoefficientPositive)
  have hDifference : s₁.logRatio - s₂.logRatio = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hCoefficientNonzero
  linarith

/-- Equal RG data and equal subtraction scale select the same condensate. -/
theorem stationary_condensate_unique
    (s₁ s₂ : OneLogCompositeVacuum)
    (hMu : s₁.renormalizationMass = s₂.renormalizationMass)
    (hLambda : s₁.sexticCoupling = s₂.sexticCoupling)
    (hCoefficient : s₁.logCoefficient = s₂.logCoefficient) :
    s₁.condensateMass = s₂.condensateMass := by
  have hLog := stationary_log_ratio_unique s₁ s₂ hLambda hCoefficient
  calc
    s₁.condensateMass =
        s₁.renormalizationMass * Real.exp s₁.logRatio :=
      s₁.condensateLaw
    _ = s₂.renormalizationMass * Real.exp s₂.logRatio := by
      rw [hMu, hLog]
    _ = s₂.condensateMass := s₂.condensateLaw.symm

/-- Vacuum energy at the stationary point. -/
def stationaryVacuumEnergy (s : OneLogCompositeVacuum) : ℝ :=
  -(s.logCoefficient * s.condensateMass ^ 3 / 3)

/-- Curvature with respect to the composite coordinate at the stationary point. -/
def stationaryCompositeCurvature (s : OneLogCompositeVacuum) : ℝ :=
  3 * s.logCoefficient * s.condensateMass

/-- Positive logarithmic coefficient gives negative stationary vacuum energy. -/
theorem stationary_vacuum_energy_is_negative
    (s : OneLogCompositeVacuum) :
    stationaryVacuumEnergy s < 0 := by
  unfold stationaryVacuumEnergy
  have hPower : 0 < s.condensateMass ^ 3 :=
    pow_pos s.condensateMassPositive 3
  have hPositive :
      0 < s.logCoefficient * s.condensateMass ^ 3 / 3 :=
    div_pos (mul_pos s.logCoefficientPositive hPower) (by norm_num)
  linarith

/-- Positive logarithmic coefficient gives positive composite curvature. -/
theorem stationary_composite_curvature_is_positive
    (s : OneLogCompositeVacuum) :
    0 < stationaryCompositeCurvature s := by
  unfold stationaryCompositeCurvature
  exact mul_pos
    (mul_pos (by norm_num) s.logCoefficientPositive)
    s.condensateMassPositive

/-- First derivative in the logarithmic coordinate `x = log(σ/mu)`. -/
def logCoordinateDerivative
    (s : OneLogCompositeVacuum) (x : ℝ) : ℝ :=
  s.renormalizationMass ^ 3 * Real.exp (3 * x) *
    (3 * s.sexticCoupling + s.logCoefficient +
      3 * s.logCoefficient * x)

/-- The derivative factorizes around the unique stationary logarithmic point. -/
theorem derivative_factorization
    (s : OneLogCompositeVacuum) (x : ℝ) :
    logCoordinateDerivative s x =
      s.renormalizationMass ^ 3 * Real.exp (3 * x) *
        (3 * s.logCoefficient * (x - s.logRatio)) := by
  unfold logCoordinateDerivative
  have hStationary := s.stationarityBracket
  congr 1
  nlinarith [hStationary]

/-- The potential decreases below the stationary point. -/
theorem derivative_negative_below_vacuum
    (s : OneLogCompositeVacuum) (x : ℝ)
    (hBelow : x < s.logRatio) :
    logCoordinateDerivative s x < 0 := by
  rw [derivative_factorization]
  have hScalePower : 0 < s.renormalizationMass ^ 3 :=
    pow_pos s.renormalizationMassPositive 3
  have hExp : 0 < Real.exp (3 * x) := Real.exp_pos _
  have hLinear :
      3 * s.logCoefficient * (x - s.logRatio) < 0 := by
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) s.logCoefficientPositive)
      (sub_neg.mpr hBelow)
  exact mul_neg_of_pos_of_neg (mul_pos hScalePower hExp) hLinear

/-- The potential increases above the stationary point. -/
theorem derivative_positive_above_vacuum
    (s : OneLogCompositeVacuum) (x : ℝ)
    (hAbove : s.logRatio < x) :
    0 < logCoordinateDerivative s x := by
  rw [derivative_factorization]
  have hScalePower : 0 < s.renormalizationMass ^ 3 :=
    pow_pos s.renormalizationMassPositive 3
  have hExp : 0 < Real.exp (3 * x) := Real.exp_pos _
  have hLinear :
      0 < 3 * s.logCoefficient * (x - s.logRatio) := by
    exact mul_pos
      (mul_pos (by norm_num) s.logCoefficientPositive)
      (sub_pos.mpr hAbove)
  exact mul_pos (mul_pos hScalePower hExp) hLinear

/-- Attach the stable composite vacuum to the LL primitive-flux map. -/
structure OneLogAlphaVacuum extends OneLogCompositeVacuum where
  chargeAmplitude : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  chargeAmplitudePositive : 0 < chargeAmplitude
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  chargeFromCondensate :
    chargeUnit = chargeAmplitude ^ 2 * condensateMass ^ 2
  primitiveFluxRadiusLaw :
    16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Convert to the generic dimensionally consistent charge interface. -/
def asCondensateChargeAlpha
    (s : OneLogAlphaVacuum) : CondensateChargeAlpha :=
  { condensateMass := s.condensateMass
    chargeAmplitude := s.chargeAmplitude
    chargeUnit := s.chargeUnit
    alphaSquaredLength := s.alphaSquaredLength
    condensateMassPositive := s.condensateMassPositive
    chargeAmplitudePositive := s.chargeAmplitudePositive
    alphaSquaredLengthPositive := s.alphaSquaredLengthPositive
    chargeFromCondensate := s.chargeFromCondensate
    primitiveFluxRadiusLaw := s.primitiveFluxRadiusLaw }

/-- Exact stable-vacuum/LL-radius relation. -/
theorem stable_vacuum_fixes_alpha_relation
    (s : OneLogAlphaVacuum) :
    2 * s.chargeAmplitude * s.condensateMass *
        s.alphaSquaredLength = 1 := by
  exact condensate_alpha_law (asCondensateChargeAlpha s)

/--
Substituting the RG minimum gives the microscopic alpha equation
`2*a_q*mu*exp(x_*)*A = 1`.
-/
theorem microscopic_alpha_equation
    (s : OneLogAlphaVacuum) :
    2 * s.chargeAmplitude * s.renormalizationMass *
        Real.exp s.logRatio * s.alphaSquaredLength = 1 := by
  have hAlpha := stable_vacuum_fixes_alpha_relation s
  rw [s.condensateLaw] at hAlpha
  simpa [mul_assoc] using hAlpha

/-- Equal microscopic data select the same alpha length. -/
theorem same_microscopic_vacuum_data_fix_alpha
    (s₁ s₂ : OneLogAlphaVacuum)
    (hMu : s₁.renormalizationMass = s₂.renormalizationMass)
    (hLambda : s₁.sexticCoupling = s₂.sexticCoupling)
    (hCoefficient : s₁.logCoefficient = s₂.logCoefficient)
    (hAmplitude : s₁.chargeAmplitude = s₂.chargeAmplitude) :
    s₁.alphaSquaredLength = s₂.alphaSquaredLength := by
  have hCondensate := stationary_condensate_unique
    s₁.toOneLogCompositeVacuum s₂.toOneLogCompositeVacuum
    hMu hLambda hCoefficient
  have h₁ := stable_vacuum_fixes_alpha_relation s₁
  have h₂ := stable_vacuum_fixes_alpha_relation s₂
  rw [hAmplitude, hCondensate] at h₁
  have hFactorPositive :
      0 < 2 * s₂.chargeAmplitude * s₂.condensateMass := by
    exact mul_pos
      (mul_pos (by norm_num) s₂.chargeAmplitudePositive)
      s₂.condensateMassPositive
  nlinarith [h₁, h₂, hFactorPositive]

end P0EFTJanusRGImprovedSexticVacuum
end JanusFormal
