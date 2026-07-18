import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothInverseMusical4D

/-!
# Smooth holonomic scalar gradient on effective D8 backgrounds

For every smooth scalar and smooth general Lorentz metric, `sharp(dφ)` is a
genuine smooth tangent-vector field.  Its metric flattening is exactly `dφ`,
and the construction commutes with arbitrary effective D8 pullback.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8SmoothHolonomicScalarGradient4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8MusicalNaturality4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8HolonomicScalarGradientPullback4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D

private abbrev EffectiveQuotient (background : EffectiveD8Background) :=
  MappingTorus
    (reflectedSphereData background.period background.period_ne_zero)

local instance effectiveQuotientChartedSpace
    (background : EffectiveD8Background) :
    ChartedSpace CoverModel (EffectiveQuotient background) :=
  reflectedSphereQuotientChartedSpace
    background.period background.period_ne_zero

local instance effectiveQuotientIsManifold
    (background : EffectiveD8Background) :
    IsManifold coverModelWithCorners ω (EffectiveQuotient background) :=
  reflectedSphereQuotient_isManifold
    background.period background.period_ne_zero

/-- The genuine smooth metric gradient `sharp(dφ)`. -/
def effectiveD8SmoothScalarGradient
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real) :
    EffectiveD8SmoothVectorField background :=
  effectiveD8SmoothInverseMusical background metric
    (effectiveD8SmoothScalarDifferential background scalar)

@[simp] theorem effectiveD8SmoothScalarGradient_apply
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background) :
    effectiveD8SmoothScalarGradient background metric scalar point =
      inverseMetricSharp background.period background.period_ne_zero metric
        point (mfderiv coverModelWithCorners 𝓘(Real, Real) scalar point) :=
  rfl

/-- Flattening the constructed gradient recovers the actual scalar
differential. -/
theorem effectiveD8SmoothScalarGradient_flat
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background) :
    metric.musical point
        (effectiveD8SmoothScalarGradient background metric scalar point) =
      effectiveD8SmoothScalarDifferential background scalar point :=
  effectiveD8SmoothInverseMusical_flat background metric
    (effectiveD8SmoothScalarDifferential background scalar) point

/-- Canonical realization of the previously explicit holonomicity contract. -/
def effectiveD8CanonicalHolonomicScalarGradient
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real) :
    EffectiveD8SmoothHolonomicScalarGradient background metric scalar where
  vector := effectiveD8SmoothScalarGradient background metric scalar
  flat_eq_differential :=
    effectiveD8SmoothScalarGradient_flat background metric scalar

/-- The genuine smooth holonomic gradient commutes exactly with pullback. -/
theorem effectiveD8SmoothScalarGradient_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real) :
    effectiveD8SmoothVectorFieldPullback morphism
        (effectiveD8SmoothScalarGradient target metric scalar) =
      effectiveD8SmoothScalarGradient source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (pullbackEffectiveD8SmoothField Real morphism scalar) := by
  apply ContMDiffSection.ext
  intro point
  apply (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric
    |>.musical point).injective
  rw [effectiveD8MetricFlat_pullback morphism metric
      (effectiveD8SmoothScalarGradient target metric scalar) point,
    effectiveD8SmoothScalarGradient_flat target metric scalar (morphism point),
    effectiveD8SmoothScalarGradient_flat source
      (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
      (pullbackEffectiveD8SmoothField Real morphism scalar) point]
  exact congrArg (fun pulled => pulled point)
    (effectiveD8SmoothScalarDifferential_pullback morphism scalar).symm

/-- The canonical holonomic realization agrees with pullback of the target
canonical realization. -/
theorem effectiveD8CanonicalHolonomicScalarGradient_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real) :
    (effectiveD8CanonicalHolonomicScalarGradient target metric scalar
      |>.pullback morphism metric scalar).vector =
      (effectiveD8CanonicalHolonomicScalarGradient source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (pullbackEffectiveD8SmoothField Real morphism scalar)).vector :=
  effectiveD8SmoothScalarGradient_pullback morphism metric scalar

end

end P0EFTJanusEffectiveD8SmoothHolonomicScalarGradient4D
end JanusFormal
