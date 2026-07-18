import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8BackgroundCategory4D

/-!
# Natural tangent and cotangent fibers on the effective D8 family

The nonzero-period background category is equipped with its actual tangent
bundle.  Every categorical morphism acts by its manifold derivative, and the
dual derivative gives the corresponding contravariant cotangent transport.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8NaturalTangentBundle4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusEffectiveD8BackgroundCategory4D

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

/-- The genuine tangent bundle of an effective D8 background. -/
abbrev EffectiveD8TangentBundle (background : EffectiveD8Background) :=
  TangentBundle coverModelWithCorners (EffectiveQuotient background)

/-- The derivative action of an actual background diffeomorphism. -/
def effectiveD8TangentMap
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target) :
    EffectiveD8TangentBundle source → EffectiveD8TangentBundle target :=
  tangentMap coverModelWithCorners coverModelWithCorners morphism

@[simp] theorem effectiveD8TangentMap_proj
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tangent : EffectiveD8TangentBundle source) :
    (effectiveD8TangentMap morphism tangent).proj =
      morphism tangent.proj :=
  tangentMap_proj

/-- The identity background diffeomorphism acts identically on the tangent
bundle. -/
@[simp] theorem effectiveD8TangentMap_refl
    (background : EffectiveD8Background)
    (tangent : EffectiveD8TangentBundle background) :
    effectiveD8TangentMap
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) tangent = tangent := by
  change tangentMap coverModelWithCorners coverModelWithCorners
      (id : EffectiveQuotient background → EffectiveQuotient background)
      tangent = tangent
  exact congrFun tangentMap_id tangent

/-- Tangent transport is exactly functorial under categorical composition. -/
theorem effectiveD8TangentMap_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (tangent : EffectiveD8TangentBundle source) :
    effectiveD8TangentMap second (effectiveD8TangentMap first tangent) =
      effectiveD8TangentMap (first.trans second) tangent := by
  change tangentMap coverModelWithCorners coverModelWithCorners second
      (tangentMap coverModelWithCorners coverModelWithCorners first tangent) =
    tangentMap coverModelWithCorners coverModelWithCorners
      (first.trans second) tangent
  rw [show (first.trans second : EffectiveQuotient source →
      EffectiveQuotient target) = second ∘ first by rfl]
  exact (tangentMap_comp_at tangent
    (second.contMDiff.mdifferentiableAt (by simp))
    (first.contMDiff.mdifferentiableAt (by simp))).symm

/-- The derivative of a categorical morphism is a continuous linear
equivalence on every actual tangent fiber. -/
def effectiveD8TangentFiberEquiv
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source) :
    TangentSpace coverModelWithCorners point ≃L[Real]
      TangentSpace coverModelWithCorners (morphism point) :=
  morphism.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) point

theorem effectiveD8TangentFiberEquiv_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source)
    (tangent : TangentSpace coverModelWithCorners point) :
    effectiveD8TangentFiberEquiv morphism point tangent =
      mfderiv coverModelWithCorners coverModelWithCorners morphism point
        tangent := by
  change (morphism.isLocalDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) point) tangent = _
  exact congrArg (fun derivative => derivative tangent)
    (IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
      morphism.isLocalDiffeomorph (by simp) point)

/-- Actual cotangent fibers dual to the quotient tangent fibers. -/
abbrev EffectiveD8CotangentFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentSpace coverModelWithCorners point →L[Real] Real

/-- Contravariant dual transport on cotangent fibers. -/
def effectiveD8CotangentPullbackFiberEquiv
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source) :
    EffectiveD8CotangentFiber target (morphism point) ≃L[Real]
      EffectiveD8CotangentFiber source point :=
  (effectiveD8TangentFiberEquiv morphism point).symm.arrowCongr
    (ContinuousLinearEquiv.refl Real Real)

@[simp] theorem effectiveD8CotangentPullbackFiberEquiv_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source)
    (covector : EffectiveD8CotangentFiber target (morphism point))
    (tangent : TangentSpace coverModelWithCorners point) :
    effectiveD8CotangentPullbackFiberEquiv morphism point covector tangent =
      covector (effectiveD8TangentFiberEquiv morphism point tangent) :=
  rfl

/-- Cotangent pullback by the identity is the identity on every fiber. -/
@[simp] theorem effectiveD8CotangentPullbackFiberEquiv_refl
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background)
    (covector : EffectiveD8CotangentFiber background point) :
    effectiveD8CotangentPullbackFiberEquiv
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) point covector = covector := by
  apply ContinuousLinearMap.ext
  intro tangent
  change covector
      (mfderiv coverModelWithCorners coverModelWithCorners
        (id : EffectiveQuotient background → EffectiveQuotient background)
        point tangent) = covector tangent
  rw [mfderiv_id]
  rfl

/-- Cotangent pullback is contravariantly functorial on three arbitrary
nonzero-period effective backgrounds. -/
theorem effectiveD8CotangentPullbackFiberEquiv_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (point : EffectiveQuotient source)
    (covector : EffectiveD8CotangentFiber target (second (first point))) :
    effectiveD8CotangentPullbackFiberEquiv first point
        (effectiveD8CotangentPullbackFiberEquiv second (first point)
          covector) =
      effectiveD8CotangentPullbackFiberEquiv (first.trans second) point
        covector := by
  apply ContinuousLinearMap.ext
  intro tangent
  simp only [effectiveD8CotangentPullbackFiberEquiv_apply,
    effectiveD8TangentFiberEquiv_apply]
  rw [show (first.trans second : EffectiveQuotient source →
      EffectiveQuotient target) = second ∘ first by rfl]
  rw [mfderiv_comp point
    (second.contMDiff.mdifferentiableAt (by simp))
    (first.contMDiff.mdifferentiableAt (by simp))]
  rfl

/-- Covariant rank-two tensor fibers built from the actual tangent bundle. -/
abbrev EffectiveD8CovariantTwoTensorFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentSpace coverModelWithCorners point →L[Real]
    EffectiveD8CotangentFiber background point

/-- Contravariant pullback equivalence for covariant rank-two tensors. -/
def effectiveD8CovariantTwoTensorPullbackFiberEquiv
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source) :
    EffectiveD8CovariantTwoTensorFiber target (morphism point) ≃L[Real]
      EffectiveD8CovariantTwoTensorFiber source point :=
  (effectiveD8TangentFiberEquiv morphism point).symm.arrowCongr
    (effectiveD8CotangentPullbackFiberEquiv morphism point)

@[simp] theorem effectiveD8CovariantTwoTensorPullbackFiberEquiv_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source)
    (tensor : EffectiveD8CovariantTwoTensorFiber target (morphism point))
    (first second : TangentSpace coverModelWithCorners point) :
    effectiveD8CovariantTwoTensorPullbackFiberEquiv morphism point tensor
        first second =
      tensor (effectiveD8TangentFiberEquiv morphism point first)
        (effectiveD8TangentFiberEquiv morphism point second) :=
  rfl

/-- Tensor pullback by the identity is the identity on every rank-two fiber. -/
@[simp] theorem effectiveD8CovariantTwoTensorPullbackFiberEquiv_refl
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background)
    (tensor : EffectiveD8CovariantTwoTensorFiber background point) :
    effectiveD8CovariantTwoTensorPullbackFiberEquiv
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) point tensor = tensor := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change tensor
      (mfderiv coverModelWithCorners coverModelWithCorners
        (id : EffectiveQuotient background → EffectiveQuotient background)
        point first)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (id : EffectiveQuotient background → EffectiveQuotient background)
        point second) = tensor first second
  rw [mfderiv_id]
  rfl

/-- Rank-two tensor pullback is contravariantly functorial. -/
theorem effectiveD8CovariantTwoTensorPullbackFiberEquiv_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (point : EffectiveQuotient source)
    (tensor : EffectiveD8CovariantTwoTensorFiber target
      (second (first point))) :
    effectiveD8CovariantTwoTensorPullbackFiberEquiv first point
        (effectiveD8CovariantTwoTensorPullbackFiberEquiv second
          (first point) tensor) =
      effectiveD8CovariantTwoTensorPullbackFiberEquiv
        (first.trans second) point tensor := by
  apply ContinuousLinearMap.ext
  intro firstTangent
  apply ContinuousLinearMap.ext
  intro secondTangent
  simp only [effectiveD8CovariantTwoTensorPullbackFiberEquiv_apply,
    effectiveD8TangentFiberEquiv_apply]
  rw [show (first.trans second : EffectiveQuotient source →
      EffectiveQuotient target) = second ∘ first by rfl]
  rw [mfderiv_comp point
    (second.contMDiff.mdifferentiableAt (by simp))
    (first.contMDiff.mdifferentiableAt (by simp))]
  rfl

/-- Pointwise symmetry for an actual covariant two-tensor fiber. -/
def IsSymmetricEffectiveD8CovariantTwoTensor
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background)
    (tensor : EffectiveD8CovariantTwoTensorFiber background point) : Prop :=
  ∀ first second, tensor first second = tensor second first

/-- Pullback along every background diffeomorphism preserves symmetry. -/
theorem effectiveD8CovariantTwoTensorPullbackFiberEquiv_symmetric
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source)
    (tensor : EffectiveD8CovariantTwoTensorFiber target (morphism point))
    (hTensor : IsSymmetricEffectiveD8CovariantTwoTensor target
      (morphism point) tensor) :
    IsSymmetricEffectiveD8CovariantTwoTensor source point
      (effectiveD8CovariantTwoTensorPullbackFiberEquiv morphism point
        tensor) := by
  intro first second
  simp only [effectiveD8CovariantTwoTensorPullbackFiberEquiv_apply]
  exact hTensor _ _

end

end P0EFTJanusEffectiveD8NaturalTangentBundle4D
end JanusFormal
