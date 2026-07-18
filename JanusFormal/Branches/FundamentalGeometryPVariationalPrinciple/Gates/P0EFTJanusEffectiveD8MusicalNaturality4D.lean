import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

/-!
# Musical naturality on the global effective D8 category

The smooth metric, tangent-vector and cotangent-field pullbacks are compatible:
lowering an index commutes exactly with pullback between arbitrary nonzero
periods.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8MusicalNaturality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8NaturalTangentBundle4D
open P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

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

/-- Lowering the pulled-back vector with the pulled-back metric is exactly the
cotangent pullback of the target lowered vector. -/
theorem effectiveD8MetricFlat_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (field : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source) :
    (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric).musical point
        (effectiveD8SmoothVectorFieldPullback morphism field point) =
      effectiveD8CotangentPullbackFiberEquiv morphism point
        (metric.musical (morphism point) (field (morphism point))) := by
  apply ContinuousLinearMap.ext
  intro tangent
  change metric.musical (morphism point)
      (effectiveD8TangentFiberEquiv morphism point
        (effectiveD8SmoothVectorFieldPullback morphism field point))
      (effectiveD8TangentFiberEquiv morphism point tangent) =
    metric.musical (morphism point) (field (morphism point))
      (effectiveD8TangentFiberEquiv morphism point tangent)
  simp only [effectiveD8TangentFiberEquiv_apply,
    effectiveD8SmoothVectorFieldPullback_apply,
    VectorField.mpullback_apply]
  have hInvertible :
      (mfderiv coverModelWithCorners coverModelWithCorners
        morphism point).IsInvertible := by
    rw [← morphism.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [hInvertible.self_apply_inverse]

/-- If a supplied smooth target one-form is the metric flattening of a smooth
target vector field, the same equality holds after global pullback. -/
theorem effectiveD8MetricFlatSection_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (field : EffectiveD8SmoothVectorField target)
    (covector : EffectiveD8SmoothCovectorField target)
    (hFlat : ∀ point, covector point = metric.musical point (field point))
    (point : EffectiveQuotient source) :
    effectiveD8SmoothCovectorFieldPullback morphism covector point =
      (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric).musical
        point (effectiveD8SmoothVectorFieldPullback morphism field point) := by
  change effectiveD8CotangentPullbackFiberEquiv morphism point
      (covector (morphism point)) = _
  rw [hFlat (morphism point)]
  exact (effectiveD8MetricFlat_pullback morphism metric field point).symm

/-- Musical compatibility is pointwise unique: any pulled covector satisfying
the target flat relation is the one produced by the cotangent functor. -/
theorem effectiveD8MetricFlatSection_pullback_unique
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (field : EffectiveD8SmoothVectorField target)
    (covector : EffectiveD8SmoothCovectorField target)
    (hFlat : ∀ point, covector point = metric.musical point (field point))
    (candidate : EffectiveD8SmoothCovectorField source)
    (hCandidate : ∀ point,
      candidate point =
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric).musical
          point (effectiveD8SmoothVectorFieldPullback morphism field point)) :
    candidate = effectiveD8SmoothCovectorFieldPullback morphism covector := by
  apply ContMDiffSection.ext
  intro point
  rw [hCandidate point,
    ← effectiveD8MetricFlatSection_pullback morphism metric field covector
      hFlat point]

end

end P0EFTJanusEffectiveD8MusicalNaturality4D
end JanusFormal
