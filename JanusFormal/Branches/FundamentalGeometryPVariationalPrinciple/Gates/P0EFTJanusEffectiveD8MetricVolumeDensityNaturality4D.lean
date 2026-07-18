import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D

/-!
# Natural metric Gram determinants and volume densities

A four-frame of genuine smooth vector fields pulls back componentwise.  The
metric Gram matrix, its determinant and the associated absolute square-root
volume density are exactly natural between arbitrary effective D8 backgrounds.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D

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

/-- A smooth ordered four-frame, without a pointwise basis assumption. -/
abbrev EffectiveD8SmoothVectorFrame (background : EffectiveD8Background) :=
  Fin 4 → EffectiveD8SmoothVectorField background

/-- Componentwise pullback of a smooth four-frame. -/
def effectiveD8SmoothVectorFramePullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (frame : EffectiveD8SmoothVectorFrame target) :
    EffectiveD8SmoothVectorFrame source :=
  fun index => effectiveD8SmoothVectorFieldPullback morphism (frame index)

/-- Exact naturality of the metric Gram matrix evaluated on a smooth frame. -/
theorem effectiveD8MetricGramMatrix_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (point : EffectiveQuotient source) :
    metricGramMatrix source.period source.period_ne_zero
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric) point
        (fun index => effectiveD8SmoothVectorFramePullback morphism frame index
          point) =
      metricGramMatrix target.period target.period_ne_zero metric
        (morphism point) (fun index => frame index (morphism point)) := by
  ext first second
  exact effectiveD8LorentzMetricVectorContraction_pullback morphism metric
    (frame first) (frame second) point

/-- The Gram determinant is exactly invariant under simultaneous metric/frame
pullback. -/
theorem effectiveD8MetricGramDeterminant_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (point : EffectiveQuotient source) :
    (metricGramMatrix source.period source.period_ne_zero
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric) point
        (fun index => effectiveD8SmoothVectorFramePullback morphism frame index
          point)).det =
      (metricGramMatrix target.period target.period_ne_zero metric
        (morphism point) (fun index => frame index (morphism point))).det := by
  rw [effectiveD8MetricGramMatrix_pullback morphism metric frame point]

/-- Consequently the absolute metric volume density is natural. -/
theorem effectiveD8MetricVolumeDensity_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (point : EffectiveQuotient source) :
    metricVolumeDensity source.period source.period_ne_zero
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric) point
        (fun index => effectiveD8SmoothVectorFramePullback morphism frame index
          point) =
      metricVolumeDensity target.period target.period_ne_zero metric
        (morphism point) (fun index => frame index (morphism point)) := by
  unfold metricVolumeDensity
  rw [effectiveD8MetricGramDeterminant_pullback morphism metric frame point]

/-- Nonvanishing of the chosen-frame density is transported in both
directions. -/
theorem effectiveD8MetricVolumeDensity_pullback_ne_zero_iff
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame target)
    (point : EffectiveQuotient source) :
    metricVolumeDensity source.period source.period_ne_zero
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric) point
        (fun index => effectiveD8SmoothVectorFramePullback morphism frame index
          point) ≠ 0 ↔
      metricVolumeDensity target.period target.period_ne_zero metric
        (morphism point) (fun index => frame index (morphism point)) ≠ 0 := by
  rw [effectiveD8MetricVolumeDensity_pullback morphism metric frame point]

end

end P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D
end JanusFormal
