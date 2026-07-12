import Mathlib

namespace JanusFormal
namespace P0EFTJanusHeatKernelCountertermScheme

set_option autoImplicit false

/--
Stationarity equation for a local linear term plus the exact-quarter nonlocal
determinant. With `y = exp(2*x) > 1`, the derivative equation is

`c * (y + 1) = 2*w`,

where `c` is the finite local coefficient and `w` the positive nonlocal weight.
-/
def QuarterCountertermStationarity
    (localCoefficient nonlocalWeight exponent : ℝ) : Prop :=
  localCoefficient * (exponent + 1) = 2 * nonlocalWeight

/-- Candidate stationary exponential. -/
noncomputable def stationaryExponent
    (localCoefficient nonlocalWeight : ℝ) : ℝ :=
  2 * nonlocalWeight / localCoefficient - 1

/-- The candidate solves the stationarity equation. -/
theorem stationary_exponent_solves_equation
    (localCoefficient nonlocalWeight : ℝ)
    (hLocal : localCoefficient ≠ 0) :
    QuarterCountertermStationarity localCoefficient nonlocalWeight
      (stationaryExponent localCoefficient nonlocalWeight) := by
  unfold QuarterCountertermStationarity stationaryExponent
  field_simp [hLocal]
  ring

/-- The stationary exponential is unique once the finite local coefficient is fixed. -/
theorem stationary_exponent_unique
    (localCoefficient nonlocalWeight exponent : ℝ)
    (hLocal : localCoefficient ≠ 0)
    (hStationary :
      QuarterCountertermStationarity localCoefficient nonlocalWeight exponent) :
    exponent = stationaryExponent localCoefficient nonlocalWeight := by
  unfold QuarterCountertermStationarity at hStationary
  unfold stationaryExponent
  apply (eq_sub_iff_add_eq).2
  apply (eq_div_iff hLocal).2
  nlinarith [hStationary]

/-- Physical finite-modulus stationarity requires `0<c<w`. -/
theorem physical_stationary_exponent_gt_one
    (localCoefficient nonlocalWeight : ℝ)
    (hLocal : 0 < localCoefficient)
    (hBelowWeight : localCoefficient < nonlocalWeight) :
    1 < stationaryExponent localCoefficient nonlocalWeight := by
  have hRatio : 2 < 2 * nonlocalWeight / localCoefficient := by
    apply (lt_div_iff₀ hLocal).2
    nlinarith
  unfold stationaryExponent
  linarith

/-- Finite local coefficient that places the stationary point at a chosen exponent. -/
noncomputable def coefficientForTarget
    (nonlocalWeight targetExponent : ℝ) : ℝ :=
  2 * nonlocalWeight / (targetExponent + 1)

/-- Every positive target exponent admits a positive fitting coefficient. -/
theorem target_coefficient_positive
    (nonlocalWeight targetExponent : ℝ)
    (hWeight : 0 < nonlocalWeight)
    (hTarget : 1 < targetExponent) :
    0 < coefficientForTarget nonlocalWeight targetExponent := by
  unfold coefficientForTarget
  exact div_pos (by nlinarith) (by linarith)

/-- For a physical target `y>1`, the fitting coefficient lies below the nonlocal weight. -/
theorem target_coefficient_below_weight
    (nonlocalWeight targetExponent : ℝ)
    (hWeight : 0 < nonlocalWeight)
    (hTarget : 1 < targetExponent) :
    coefficientForTarget nonlocalWeight targetExponent < nonlocalWeight := by
  unfold coefficientForTarget
  have hDen : 0 < targetExponent + 1 := by linarith
  apply (div_lt_iff₀ hDen).2
  nlinarith

/-- The fitted coefficient makes the chosen exponent exactly stationary. -/
theorem target_coefficient_fits_target
    (nonlocalWeight targetExponent : ℝ)
    (hTarget : targetExponent + 1 ≠ 0) :
    QuarterCountertermStationarity
      (coefficientForTarget nonlocalWeight targetExponent)
      nonlocalWeight targetExponent := by
  unfold QuarterCountertermStationarity coefficientForTarget
  field_simp [hTarget]

/-- Positive curvature proxy of the quarter-holonomy nonlocal term. -/
noncomputable def quarterCurvature
    (nonlocalWeight exponent : ℝ) : ℝ :=
  4 * nonlocalWeight * exponent / (exponent + 1) ^ 2

/-- The fitted stationary point is locally stable for positive weight and exponent. -/
theorem quarter_curvature_positive
    (nonlocalWeight exponent : ℝ)
    (hWeight : 0 < nonlocalWeight)
    (hExponent : 0 < exponent)
    (hNotMinusOne : exponent + 1 ≠ 0) :
    0 < quarterCurvature nonlocalWeight exponent := by
  unfold quarterCurvature
  exact div_pos
    (mul_pos (mul_pos (by norm_num) hWeight) hExponent)
    (sq_pos_of_ne_zero hNotMinusOne)

/--
Any desired positive finite modulus can be reproduced by choosing a finite local
counterterm. Therefore the local-plus-quarter determinant model is not
predictive until a separate theorem fixes the finite coefficient.
-/
theorem every_target_modulus_can_be_fitted
    (nonlocalWeight targetExponent : ℝ)
    (hWeight : 0 < nonlocalWeight)
    (hTarget : 1 < targetExponent) :
    ∃ localCoefficient : ℝ,
      0 < localCoefficient /\
      localCoefficient < nonlocalWeight /\
      QuarterCountertermStationarity localCoefficient
        nonlocalWeight targetExponent /\
      0 < quarterCurvature nonlocalWeight targetExponent := by
  refine ⟨coefficientForTarget nonlocalWeight targetExponent,
    target_coefficient_positive nonlocalWeight targetExponent hWeight hTarget,
    target_coefficient_below_weight nonlocalWeight targetExponent hWeight hTarget,
    ?_, ?_⟩
  · exact target_coefficient_fits_target nonlocalWeight targetExponent
      (by linarith)
  · exact quarter_curvature_positive nonlocalWeight targetExponent
      hWeight (by linarith) (by linarith)

/-- Two different target exponents require different finite coefficients. -/
theorem distinct_targets_require_distinct_coefficients
    (nonlocalWeight firstTarget secondTarget : ℝ)
    (hWeight : nonlocalWeight ≠ 0)
    (hFirstDen : firstTarget + 1 ≠ 0)
    (hSecondDen : secondTarget + 1 ≠ 0)
    (hTargets : firstTarget ≠ secondTarget) :
    coefficientForTarget nonlocalWeight firstTarget ≠
      coefficientForTarget nonlocalWeight secondTarget := by
  intro hEqual
  unfold coefficientForTarget at hEqual
  field_simp [hFirstDen, hSecondDen] at hEqual
  apply hTargets
  nlinarith [hEqual, hWeight]

/--
A predictive spectral theory must derive the finite local coefficient from a
symmetry, matching condition, UV completion or target-independent
renormalization principle. Merely choosing it to obtain the desired radius is
mathematically equivalent to fitting the radius.
-/
structure CountertermPredictivityStatus where
  localHeatCoefficientsComputed : Prop
  divergentCountertermsSubtracted : Prop
  finiteRenormalizedCoefficientDerived : Prop
  renormalizationConditionIndependentOfTargetRadius : Prop
  nonlocalQuarterDeterminantComputed : Prop
  stableModulusDerived : Prop
  schemeIndependenceProved : Prop


def countertermPredictivityClosed
    (s : CountertermPredictivityStatus) : Prop :=
  s.localHeatCoefficientsComputed /\
  s.divergentCountertermsSubtracted /\
  s.finiteRenormalizedCoefficientDerived /\
  s.renormalizationConditionIndependentOfTargetRadius /\
  s.nonlocalQuarterDeterminantComputed /\
  s.stableModulusDerived /\
  s.schemeIndependenceProved

end P0EFTJanusHeatKernelCountertermScheme
end JanusFormal
