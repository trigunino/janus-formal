import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D

/-!
# Natural tensor/vector contraction on the effective D8 family

The contravariant covariant-two-tensor pullback and the contravariant vector
field pullback cancel their derivative factors exactly.  Hence scalar
contractions are natural between arbitrary nonzero-period backgrounds.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D

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

/-- Exact naturality of the bilinear tensor/vector contraction. -/
theorem effectiveD8TensorVectorContraction_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source) :
    (effectiveD8SmoothSymmetricTensorPullback morphism tensor).tensor point
        (effectiveD8SmoothVectorFieldPullback morphism first point)
        (effectiveD8SmoothVectorFieldPullback morphism second point) =
      tensor.tensor (morphism point) (first (morphism point))
        (second (morphism point)) := by
  change effectiveD8SmoothTensorPullbackField morphism tensor point
      (effectiveD8SmoothVectorFieldPullback morphism first point)
      (effectiveD8SmoothVectorFieldPullback morphism second point) = _
  rw [effectiveD8SmoothTensorPullbackField_apply]
  simp only [effectiveD8SmoothVectorFieldPullback_apply,
    VectorField.mpullback_apply]
  have hInvertible :
      (mfderiv coverModelWithCorners coverModelWithCorners
        morphism point).IsInvertible := by
    rw [← morphism.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [hInvertible.self_apply_inverse, hInvertible.self_apply_inverse]

/-- In particular, the quadratic scalar `T(X,X)` is natural. -/
theorem effectiveD8TensorVectorQuadratic_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (field : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source) :
    (effectiveD8SmoothSymmetricTensorPullback morphism tensor).tensor point
        (effectiveD8SmoothVectorFieldPullback morphism field point)
        (effectiveD8SmoothVectorFieldPullback morphism field point) =
      tensor.tensor (morphism point) (field (morphism point))
        (field (morphism point)) :=
  effectiveD8TensorVectorContraction_pullback morphism tensor field field point

/-- The same exact contraction law applies to every smooth general Lorentz
metric in the global natural metric functor. -/
theorem effectiveD8LorentzMetricVectorContraction_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source) :
    (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric).tensor.tensor
        point
        (effectiveD8SmoothVectorFieldPullback morphism first point)
        (effectiveD8SmoothVectorFieldPullback morphism second point) =
      metric.tensor.tensor (morphism point) (first (morphism point))
        (second (morphism point)) :=
  effectiveD8TensorVectorContraction_pullback morphism metric.tensor
    first second point

end

end P0EFTJanusEffectiveD8TensorVectorContractionNaturality4D
end JanusFormal
