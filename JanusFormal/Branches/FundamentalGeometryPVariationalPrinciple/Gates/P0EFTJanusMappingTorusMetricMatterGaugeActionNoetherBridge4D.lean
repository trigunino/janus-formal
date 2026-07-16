import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D

/-!
# Action-derivative bridge for the conditional metric/matter/gauge block

This gate identifies the Euler covector in the conditional two-metric,
eight-scalar and `U(1)^2` B operator with the actual derivative of an action
along every real affine line.  Finite invariance under every generated
translation is then equivalent to `B(dS) = 0` at every base variation.

The action here lives on the linear variation space around fixed background
fields and fixed intrinsic metrics.  It is not the final nonlinear Janus
action on the full field configuration space.  The metric directions remain
conditional precisely through the supplied flow-to-ghost contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMetricMatterGaugeActionNoetherBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The supplied covector is the true derivative of the fixed-background
variation action along every real line through zero. -/
def HasMetricMatterGaugeDirectionalFirstVariationAtZero
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) : Prop :=
  ∀ variation : MetricMatterGaugeVariationSpace period hPeriod,
    HasDerivAt (fun parameter : Real => action (parameter • variation))
      (euler variation) 0

/-- Finite invariance along every conditional combined line through the zero
variation. -/
def MetricMatterGaugeLineInvariantAtZero
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real) : Prop :=
  ∀ parameters : MatterGaugeParameterSpace period hPeriod,
    ∀ lineParameter : Real,
      action
          (lineParameter •
            metricMatterGaugeLinearizedVariation period hPeriod fields plusMetric
              minusMetric contract parameters) =
        action 0

/-- At the origin, finite line invariance and the true first variation imply
the conditional combined B identity. -/
theorem metricMatterGaugeNoetherOperator_eq_zero_of_action_invariant
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (hFirstVariation :
      HasMetricMatterGaugeDirectionalFirstVariationAtZero period hPeriod action euler)
    (hInvariant :
      MetricMatterGaugeLineInvariantAtZero period hPeriod fields plusMetric
        minusMetric contract action) :
    metricMatterGaugeNoetherOperator period hPeriod fields plusMetric minusMetric
      contract euler = 0 := by
  apply (metricMatterGaugeNoetherOperator_eq_zero_iff period hPeriod fields
    plusMetric minusMetric contract euler).2
  intro parameters
  let direction := metricMatterGaugeLinearizedVariation period hPeriod fields
    plusMetric minusMetric contract parameters
  have hActionDerivative := hFirstVariation direction
  have hCurveConstant :
      (fun lineParameter : Real => action (lineParameter • direction)) =
        fun _ => action 0 := by
    funext lineParameter
    exact hInvariant parameters lineParameter
  have hZeroDerivative :
      HasDerivAt (fun lineParameter : Real => action (lineParameter • direction))
        0 0 := by
    rw [hCurveConstant]
    exact hasDerivAt_const (x := (0 : Real)) (c := action 0)
  exact hActionDerivative.unique hZeroDerivative

/-- A linewise Euler one-form on the complete conditional variation space.
No Banach topology on the space of global smooth sections is introduced. -/
def HasMetricMatterGaugeLinewiseFirstVariationEverywhere
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →
      (MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)) : Prop :=
  ∀ base direction : MetricMatterGaugeVariationSpace period hPeriod,
    ∀ parameter : Real,
      HasDerivAt
        (fun lineParameter : Real => action (base + lineParameter • direction))
        (euler (base + parameter • direction) direction) parameter

/-- Finite additive invariance at every base variation under every direction
generated by the same conditional metric/matter/gauge block. -/
def MetricMatterGaugeTranslationInvariant
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real) : Prop :=
  ∀ base : MetricMatterGaugeVariationSpace period hPeriod,
    ∀ parameters : MatterGaugeParameterSpace period hPeriod,
      action
          (base + metricMatterGaugeLinearizedVariation period hPeriod fields
            plusMetric minusMetric contract parameters) =
        action base

private theorem metricMatterGauge_zero_smul
    (variation : MetricMatterGaugeVariationSpace period hPeriod) :
    (0 : Real) • variation = 0 := by
  apply Prod.ext
  · apply Prod.ext
    · apply ContMDiffSection.ext
      intro point
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact zero_mul _
    · apply ContMDiffSection.ext
      intro point
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact zero_mul _
  · apply Prod.ext
    · funext index
      apply P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField.ext
        period hPeriod Real
      intro point
      exact zero_mul _
    · apply Prod.ext
      · apply P0EFTJanusMappingTorusAbelianGaugeBRST4D.SmoothAbelianGaugePotential.ext
        intro chart point tangent
        exact congrArg
          (fun covector : TangentSpace coverModelWithCorners point →L[Real] Real =>
            covector tangent)
          (zero_smul Real (variation.2.2.1.toFun chart point))
      · apply P0EFTJanusMappingTorusAbelianGaugeBRST4D.SmoothAbelianGaugePotential.ext
        intro chart point tangent
        exact congrArg
          (fun covector : TangentSpace coverModelWithCorners point →L[Real] Real =>
            covector tangent)
          (zero_smul Real (variation.2.2.2.toFun chart point))

/-- Exact fixed-background affine bridge: with the actual line derivative
known everywhere, finite translation invariance is equivalent to vanishing of
the conditional combined B operator at every base variation. -/
theorem metricMatterGauge_translation_invariant_iff_noether_everywhere
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →
      (MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real))
    (hFirstVariation :
      HasMetricMatterGaugeLinewiseFirstVariationEverywhere period hPeriod
        action euler) :
    MetricMatterGaugeTranslationInvariant period hPeriod fields plusMetric
        minusMetric contract action ↔
      ∀ base : MetricMatterGaugeVariationSpace period hPeriod,
        metricMatterGaugeNoetherOperator period hPeriod fields plusMetric
          minusMetric contract (euler base) = 0 := by
  constructor
  · intro hInvariant base
    apply (metricMatterGaugeNoetherOperator_eq_zero_iff period hPeriod fields
      plusMetric minusMetric contract (euler base)).2
    intro parameters
    let direction := metricMatterGaugeLinearizedVariation period hPeriod fields
      plusMetric minusMetric contract parameters
    let curve : Real → Real :=
      fun parameter => action (base + parameter • direction)
    have hCurveDerivative : HasDerivAt curve (euler base direction) 0 := by
      have hDerivative := hFirstVariation base direction 0
      have hBaseZero : base + (0 : Real) • direction = base := by
        calc
          base + (0 : Real) • direction = base + 0 :=
            congrArg (fun variation => base + variation)
              (metricMatterGauge_zero_smul period hPeriod direction)
          _ = base := add_zero base
      rw [hBaseZero] at hDerivative
      simpa only [curve] using hDerivative
    have hCurveConstant : curve = fun _ => action base := by
      funext parameter
      have hTranslated := hInvariant base (parameter • parameters)
      simpa [curve, direction] using hTranslated
    have hZeroDerivative : HasDerivAt curve 0 0 := by
      rw [hCurveConstant]
      exact hasDerivAt_const (x := (0 : Real)) (c := action base)
    exact hCurveDerivative.unique hZeroDerivative
  · intro hNoether base parameters
    let direction := metricMatterGaugeLinearizedVariation period hPeriod fields
      plusMetric minusMetric contract parameters
    let curve : Real → Real :=
      fun parameter => action (base + parameter • direction)
    have hCurveDerivative (parameter : Real) : HasDerivAt curve 0 parameter := by
      have hDerivative := hFirstVariation base direction parameter
      have hHorizontal :=
        (metricMatterGaugeNoetherOperator_eq_zero_iff period hPeriod fields
          plusMetric minusMetric contract
          (euler (base + parameter • direction))).1
          (hNoether (base + parameter • direction)) parameters
      exact (by simpa [curve, direction] using
        hDerivative.congr_deriv hHorizontal)
    have hCurveDifferentiable : Differentiable Real curve :=
      fun parameter => (hCurveDerivative parameter).differentiableAt
    have hCurveDerivZero (parameter : Real) : deriv curve parameter = 0 :=
      (hCurveDerivative parameter).deriv
    have hConstant :=
      is_const_of_deriv_eq_zero hCurveDifferentiable hCurveDerivZero 1 0
    have hBaseOne : base + (1 : Real) • direction = base + direction := by
      exact congrArg (fun variation => base + variation)
        (one_smul Real direction)
    have hBaseZero : base + (0 : Real) • direction = base := by
      calc
        base + (0 : Real) • direction = base + 0 :=
          congrArg (fun variation => base + variation)
            (metricMatterGauge_zero_smul period hPeriod direction)
        _ = base := add_zero base
    dsimp only [curve] at hConstant
    rw [hBaseOne, hBaseZero] at hConstant
    exact hConstant

end

end P0EFTJanusMappingTorusMetricMatterGaugeActionNoetherBridge4D
end JanusFormal
