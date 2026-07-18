import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D

/-!
# Smooth tensor/vector contractions on the effective D8 family

Bundlewise application turns a genuine smooth covariant two-tensor and two
genuine smooth tangent fields into a genuine smooth scalar.  The resulting
scalar construction retains the exact pullback law.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
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

/-- Smooth scalar obtained by applying a smooth covariant two-tensor to two
smooth tangent fields. -/
def effectiveD8SmoothTensorVectorContraction
    (background : EffectiveD8Background)
    (tensor : SmoothSymmetricCovariantTwoTensor background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background) :
    SmoothQuotientField background.period background.period_ne_zero Real where
  toFun := fun point => tensor.tensor point (first point) (second point)
  contMDiff_toFun := by
    have hApplied := tensor.tensor.contMDiff.clm_bundle_apply₂
      first.contMDiff second.contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp] theorem effectiveD8SmoothTensorVectorContraction_apply
    (background : EffectiveD8Background)
    (tensor : SmoothSymmetricCovariantTwoTensor background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background)
    (point : EffectiveQuotient background) :
    effectiveD8SmoothTensorVectorContraction background tensor first second
        point =
      tensor.tensor point (first point) (second point) :=
  rfl

/-- Exact field-level naturality of the smooth scalar contraction. -/
theorem effectiveD8SmoothTensorVectorContraction_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target) :
    effectiveD8SmoothTensorVectorContraction source
        (effectiveD8SmoothSymmetricTensorPullback morphism tensor)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second) =
      pullbackEffectiveD8SmoothField Real morphism
        (effectiveD8SmoothTensorVectorContraction target tensor first second) := by
  apply SmoothQuotientField.ext
  intro point
  exact effectiveD8TensorVectorContraction_pullback morphism tensor first
    second point

/-- Smooth scalar contraction for a general Lorentz metric. -/
def effectiveD8SmoothLorentzMetricVectorContraction
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background) :
    SmoothQuotientField background.period background.period_ne_zero Real :=
  effectiveD8SmoothTensorVectorContraction background metric.tensor first
    second

@[simp] theorem effectiveD8SmoothLorentzMetricVectorContraction_apply
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background)
    (point : EffectiveQuotient background) :
    effectiveD8SmoothLorentzMetricVectorContraction background metric first
        second point =
      metric.tensor.tensor point (first point) (second point) :=
  rfl

/-- Exact field-level naturality for the smooth metric contraction. -/
theorem effectiveD8SmoothLorentzMetricVectorContraction_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target) :
    effectiveD8SmoothLorentzMetricVectorContraction source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second) =
      pullbackEffectiveD8SmoothField Real morphism
        (effectiveD8SmoothLorentzMetricVectorContraction target metric first
          second) :=
  effectiveD8SmoothTensorVectorContraction_pullback morphism metric.tensor
    first second

end

end P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D
end JanusFormal
