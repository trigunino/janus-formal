import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D

/-!
# Natural scalar Lagrangian density on the effective D8 family

Using a supplied smooth tangent derivative field, a smooth scalar, a general
Lorentz metric and a smooth four-frame, this gate constructs the standard
quadratic kinetic-plus-potential density and proves its exact naturality under
simultaneous pullback.  Holonomicity of the supplied derivative field is kept
separate and is not assumed silently.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8ScalarLagrangianDensityNaturality4D

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
open P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D
open P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D

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

/-- Frame-evaluated quadratic scalar density.  `derivative` is an explicit
tangent field; no unproved identification with `sharp (d scalar)` is made. -/
def effectiveD8ScalarFrameLagrangianDensity
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame background)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (derivative : EffectiveD8SmoothVectorField background)
    (massSquared : Real)
    (point : EffectiveQuotient background) : Real :=
  metricVolumeDensity background.period background.period_ne_zero metric point
      (fun index => frame index point) *
    (1 / 2 * metric.tensor.tensor point (derivative point) (derivative point) +
      1 / 2 * massSquared * (scalar point) ^ 2)

/-- Exact covariance of the complete local scalar density under simultaneous
pullback of metric, frame, scalar and supplied derivative field. -/
theorem effectiveD8ScalarFrameLagrangianDensity_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real)
    (derivative : EffectiveD8SmoothVectorField target)
    (massSquared : Real)
    (point : EffectiveQuotient source) :
    effectiveD8ScalarFrameLagrangianDensity source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFramePullback morphism frame)
        (pullbackEffectiveD8SmoothField Real morphism scalar)
        (effectiveD8SmoothVectorFieldPullback morphism derivative)
        massSquared point =
      effectiveD8ScalarFrameLagrangianDensity target metric frame scalar
        derivative massSquared (morphism point) := by
  unfold effectiveD8ScalarFrameLagrangianDensity
  rw [effectiveD8MetricVolumeDensity_pullback morphism metric frame point,
    effectiveD8LorentzMetricVectorContraction_pullback morphism metric
      derivative derivative point]
  rfl

/-- The massless specialization is natural as a direct corollary. -/
theorem effectiveD8MasslessScalarFrameLagrangianDensity_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real)
    (derivative : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source) :
    effectiveD8ScalarFrameLagrangianDensity source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFramePullback morphism frame)
        (pullbackEffectiveD8SmoothField Real morphism scalar)
        (effectiveD8SmoothVectorFieldPullback morphism derivative) 0 point =
      effectiveD8ScalarFrameLagrangianDensity target metric frame scalar
        derivative 0 (morphism point) :=
  effectiveD8ScalarFrameLagrangianDensity_pullback morphism metric frame scalar
    derivative 0 point

end

end P0EFTJanusEffectiveD8ScalarLagrangianDensityNaturality4D
end JanusFormal
