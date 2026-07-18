import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothHolonomicScalarGradient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D

/-!
# Natural holonomic scalar density on the effective D8 family

The inverse-metric contraction of the actual differential is identified with
the metric contraction of the genuine smooth field `sharp(dφ)`.  Consequently
the standard kinetic-minus-potential scalar density is exactly natural between
arbitrary nonzero-period effective backgrounds.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8HolonomicScalarDensityNaturality4D

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
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8SmoothHolonomicScalarGradient4D

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

/-- Inverse contraction of a covector equals metric contraction of its raised
vector. -/
theorem inverseMetricContraction_self_eq_sharp
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (point : EffectiveQuotient background)
    (covector : TangentSpace coverModelWithCorners point →L[Real] Real) :
    inverseMetricContraction background.period background.period_ne_zero
        metric point covector covector =
      metric.tensor.tensor point
        (inverseMetricSharp background.period background.period_ne_zero
          metric point covector)
        (inverseMetricSharp background.period background.period_ne_zero
          metric point covector) := by
  unfold inverseMetricContraction
  rw [← metric.musical_eq_tensor point]
  exact congrArg
    (fun form => form (inverseMetricSharp background.period
      background.period_ne_zero metric point covector))
    (metric_flat_inverseMetricSharp background.period
      background.period_ne_zero metric point covector) |>.symm

/-- The kinetic quadratic form of the smooth scalar gradient is exactly the
original holonomic inverse-metric contraction of `dφ`. -/
theorem effectiveD8ScalarGradientQuadratic_eq_inverseMetricContraction
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background) :
    metric.tensor.tensor point
        (effectiveD8SmoothScalarGradient background metric scalar point)
        (effectiveD8SmoothScalarGradient background metric scalar point) =
      inverseMetricContraction background.period background.period_ne_zero
        metric point
        (effectiveD8SmoothScalarDifferential background scalar point)
        (effectiveD8SmoothScalarDifferential background scalar point) := by
  exact (inverseMetricContraction_self_eq_sharp background metric point
    (effectiveD8SmoothScalarDifferential background scalar point)).symm

/-- The holonomic inverse-metric kinetic contraction is natural under global
effective D8 pullback. -/
theorem effectiveD8ScalarInverseMetricContraction_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real)
    (point : EffectiveQuotient source) :
    inverseMetricContraction source.period source.period_ne_zero
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric) point
        (effectiveD8SmoothScalarDifferential source
          (pullbackEffectiveD8SmoothField Real morphism scalar) point)
        (effectiveD8SmoothScalarDifferential source
          (pullbackEffectiveD8SmoothField Real morphism scalar) point) =
      inverseMetricContraction target.period target.period_ne_zero metric
        (morphism point)
        (effectiveD8SmoothScalarDifferential target scalar (morphism point))
        (effectiveD8SmoothScalarDifferential target scalar
          (morphism point)) := by
  rw [← effectiveD8ScalarGradientQuadratic_eq_inverseMetricContraction
      source (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
      (pullbackEffectiveD8SmoothField Real morphism scalar) point,
    ← effectiveD8ScalarGradientQuadratic_eq_inverseMetricContraction
      target metric scalar (morphism point)]
  have hGradient := congrArg (fun field => field point)
    (effectiveD8SmoothScalarGradient_pullback morphism metric scalar)
  rw [← hGradient]
  exact effectiveD8LorentzMetricVectorContraction_pullback morphism metric
    (effectiveD8SmoothScalarGradient target metric scalar)
    (effectiveD8SmoothScalarGradient target metric scalar) point

/-- Standard frame-evaluated holonomic scalar density, with the same
kinetic-minus-potential sign convention as `holonomicScalarDensity`. -/
def effectiveD8HolonomicScalarFrameDensity
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame background)
    (massSquared : Real)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background) : Real :=
  holonomicScalarDensity background.period background.period_ne_zero metric
    massSquared scalar point (fun index => frame index point)

/-- Exact naturality of the genuine holonomic scalar density. -/
theorem effectiveD8HolonomicScalarFrameDensity_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (massSquared : Real)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real)
    (point : EffectiveQuotient source) :
    effectiveD8HolonomicScalarFrameDensity source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFramePullback morphism frame) massSquared
        (pullbackEffectiveD8SmoothField Real morphism scalar) point =
      effectiveD8HolonomicScalarFrameDensity target metric frame massSquared
        scalar (morphism point) := by
  unfold effectiveD8HolonomicScalarFrameDensity holonomicScalarDensity
  rw [effectiveD8MetricVolumeDensity_pullback morphism metric frame point]
  rw [show scalarDifferential source.period source.period_ne_zero
        (pullbackEffectiveD8SmoothField Real morphism scalar) point =
      effectiveD8SmoothScalarDifferential source
        (pullbackEffectiveD8SmoothField Real morphism scalar) point by rfl]
  rw [show scalarDifferential target.period target.period_ne_zero scalar
        (morphism point) =
      effectiveD8SmoothScalarDifferential target scalar (morphism point) by
        rfl]
  rw [effectiveD8ScalarInverseMetricContraction_pullback morphism metric scalar
    point]
  rfl

end

end P0EFTJanusEffectiveD8HolonomicScalarDensityNaturality4D
end JanusFormal
