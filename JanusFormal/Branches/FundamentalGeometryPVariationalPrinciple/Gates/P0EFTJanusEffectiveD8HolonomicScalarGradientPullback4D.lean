import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8MusicalNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8ScalarLagrangianDensityNaturality4D

/-!
# Pullback stability of smooth holonomic scalar gradients

A supplied smooth tangent field is certified as the scalar gradient by the
intrinsic relation `g♭ X = dφ`.  This certificate, and the associated local
scalar density, are preserved exactly by effective D8 pullback.  Existence of
the smooth inverse-musical field is not assumed here.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8HolonomicScalarGradientPullback4D

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
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8MusicalNaturality4D
open P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D
open P0EFTJanusEffectiveD8ScalarLagrangianDensityNaturality4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D

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

/-- A smooth tangent field certified to be the metric gradient of `scalar`. -/
structure EffectiveD8SmoothHolonomicScalarGradient
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real) where
  vector : EffectiveD8SmoothVectorField background
  flat_eq_differential : ∀ point,
    metric.musical point (vector point) =
      effectiveD8SmoothScalarDifferential background scalar point

/-- Pullback preserves the exact holonomicity certificate. -/
def EffectiveD8SmoothHolonomicScalarGradient.pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real)
    (gradient : EffectiveD8SmoothHolonomicScalarGradient target metric scalar) :
    EffectiveD8SmoothHolonomicScalarGradient source
      (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
      (pullbackEffectiveD8SmoothField Real morphism scalar) where
  vector := effectiveD8SmoothVectorFieldPullback morphism gradient.vector
  flat_eq_differential := by
    intro point
    rw [effectiveD8MetricFlat_pullback morphism metric gradient.vector point,
      gradient.flat_eq_differential (morphism point)]
    exact congrArg (fun pulled => pulled point)
      (effectiveD8SmoothScalarDifferential_pullback morphism scalar).symm

/-- The density built from a certified holonomic gradient has the same exact
pullback law as the supplied-vector density. -/
theorem effectiveD8HolonomicScalarFrameLagrangianDensity_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real)
    (gradient : EffectiveD8SmoothHolonomicScalarGradient target metric scalar)
    (massSquared : Real)
    (point : EffectiveQuotient source) :
    effectiveD8ScalarFrameLagrangianDensity source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFramePullback morphism frame)
        (pullbackEffectiveD8SmoothField Real morphism scalar)
        (gradient.pullback morphism metric scalar).vector massSquared point =
      effectiveD8ScalarFrameLagrangianDensity target metric frame scalar
        gradient.vector massSquared (morphism point) :=
  effectiveD8ScalarFrameLagrangianDensity_pullback morphism metric frame scalar
    gradient.vector massSquared point

end

end P0EFTJanusEffectiveD8HolonomicScalarGradientPullback4D
end JanusFormal
