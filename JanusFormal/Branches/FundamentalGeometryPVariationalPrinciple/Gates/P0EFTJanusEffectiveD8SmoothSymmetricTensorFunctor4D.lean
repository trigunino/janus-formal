import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8NaturalTangentBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D

/-!
# Smooth symmetric tensor pullback on the effective D8 family

The fiberwise covariant-two-tensor transport is promoted to genuine smooth
sections between arbitrary nonzero-period effective backgrounds.  Identity
and composition hold exactly.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8NaturalTangentBundle4D

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

private abbrev TangentFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentFiber background point →L[Real] Real

private abbrev CovariantTwoTensorFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentFiber background point →L[Real] CotangentFiber background point

private abbrev CovariantTwoTensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

/-- Fiberwise pullback of a smooth target tensor. -/
def effectiveD8SmoothTensorPullbackField
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero) :
    ∀ point : EffectiveQuotient source,
      CovariantTwoTensorFiber source point :=
  fun point => effectiveD8CovariantTwoTensorPullbackFiberEquiv morphism point
    (tensor.tensor (morphism point))

@[simp] theorem effectiveD8SmoothTensorPullbackField_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (point : EffectiveQuotient source)
    (first second : TangentFiber source point) :
    effectiveD8SmoothTensorPullbackField morphism tensor point first second =
      tensor.tensor (morphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners morphism point
          first)
        (mfderiv coverModelWithCorners coverModelWithCorners morphism point
          second) := by
  unfold effectiveD8SmoothTensorPullbackField
  rw [effectiveD8CovariantTwoTensorPullbackFiberEquiv_apply,
    effectiveD8TangentFiberEquiv_apply,
    effectiveD8TangentFiberEquiv_apply]

private def derivativeCoordinates
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point current : EffectiveQuotient source) :
    CoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates coverModelWithCorners coverModelWithCorners
    id morphism
    (mfderiv coverModelWithCorners coverModelWithCorners morphism)
    point current

private def tensorCoordinates
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (point current : EffectiveQuotient source) :
    CovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber target)
    (CoverCoordinates →L[Real] Real) (CotangentFiber target)
    (morphism point) (morphism current)
    (morphism point) (morphism current)
    (tensor.tensor (morphism current))

private def pullbackTensorCoordinates
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (point current : EffectiveQuotient source) :
    CovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber source)
    (CoverCoordinates →L[Real] Real) (CotangentFiber source)
    point current point current
    (effectiveD8SmoothTensorPullbackField morphism tensor current)

private def coordinatePullback
    (derivative : CoverCoordinates →L[Real] CoverCoordinates)
    (tensor : CovariantTwoTensorModel) : CovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem derivativeCoordinates_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point current : EffectiveQuotient source)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber source) point).baseSet)
    (hImage : morphism current ∈
      (trivializationAt CoverCoordinates (TangentFiber target)
        (morphism point)).baseSet)
    (vector : CoverCoordinates) :
    derivativeCoordinates morphism point current vector =
      (trivializationAt CoverCoordinates (TangentFiber target)
        (morphism point)).linearMapAt Real (morphism current)
          (mfderiv coverModelWithCorners coverModelWithCorners morphism
            current
            ((trivializationAt CoverCoordinates (TangentFiber source)
              point).symm current vector)) := by
  rw [show derivativeCoordinates morphism point current =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber source)
        CoverCoordinates (TangentFiber target)
        point current (morphism point) (morphism current)
        (mfderiv coverModelWithCorners coverModelWithCorners morphism
          current) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem pullbackTensorCoordinates_eq
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (point current : EffectiveQuotient source)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber source) point).baseSet)
    (hImage : morphism current ∈
      (trivializationAt CoverCoordinates (TangentFiber target)
        (morphism point)).baseSet) :
    pullbackTensorCoordinates morphism tensor point current =
      coordinatePullback
        (derivativeCoordinates morphism point current)
        (tensorCoordinates morphism tensor point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show pullbackTensorCoordinates morphism tensor point current
      first second =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber source)
        (CoverCoordinates →L[Real] Real) (CotangentFiber source)
        point current point current
        (effectiveD8SmoothTensorPullbackField morphism tensor current)
        first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [effectiveD8SmoothTensorPullbackField_apply, coordinatePullback,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  rw [show tensorCoordinates morphism tensor point current
        (derivativeCoordinates morphism point current first)
        (derivativeCoordinates morphism point current second) =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber target)
        (CoverCoordinates →L[Real] Real) (CotangentFiber target)
        (morphism point) (morphism current)
        (morphism point) (morphism current)
        (tensor.tensor (morphism current))
        (derivativeCoordinates morphism point current first)
        (derivativeCoordinates morphism point current second) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [derivativeCoordinates_apply morphism point current hCurrent hImage first,
    derivativeCoordinates_apply morphism point current hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

/-- Pullback of a smooth target tensor is a smooth source tensor section. -/
theorem effectiveD8SmoothTensorPullbackField_contMDiff
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero) :
    ContMDiff coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, CovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' CovariantTwoTensorModel
        (E := CovariantTwoTensorFiber source) point
        (effectiveD8SmoothTensorPullbackField morphism tensor point)) := by
  intro point
  have hD := morphism.contMDiff.contMDiffAt.mfderiv_const
    (x₀ := point) (m := ∞) (by simp)
  have hMap := morphism.contMDiff.of_le (m := ∞) (by simp)
  have hTensor := tensor.tensor.contMDiff.comp hMap
  have hTensorAt := hTensor point
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hD.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hD
  have hFormula := hPre.clm_comp hOuter
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply hFormula.congr_of_eventuallyEq
  have hCurrent : ∀ᶠ current in 𝓝 point,
      current ∈
        (trivializationAt CoverCoordinates (TangentFiber source) point).baseSet :=
    (trivializationAt CoverCoordinates (TangentFiber source) point).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt CoverCoordinates
        (TangentFiber source) point)
  have hImage : ∀ᶠ current in 𝓝 point,
      morphism current ∈
        (trivializationAt CoverCoordinates (TangentFiber target)
          (morphism point)).baseSet :=
    morphism.continuous.continuousAt
      ((trivializationAt CoverCoordinates (TangentFiber target)
        (morphism point)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates
            (TangentFiber target) (morphism point)))
  filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
  simpa only [pullbackTensorCoordinates, coordinatePullback,
    derivativeCoordinates, tensorCoordinates, Function.comp_apply] using
      (pullbackTensorCoordinates_eq morphism tensor point current
        hCurrent' hImage')

/-- Genuine smooth symmetric tensor pullback between different backgrounds. -/
def effectiveD8SmoothSymmetricTensorPullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero) :
    SmoothSymmetricCovariantTwoTensor source.period source.period_ne_zero where
  tensor :=
    { toFun := effectiveD8SmoothTensorPullbackField morphism tensor
      contMDiff_toFun :=
        effectiveD8SmoothTensorPullbackField_contMDiff morphism tensor }
  symmetric := by
    intro point first second
    change effectiveD8SmoothTensorPullbackField morphism tensor point
        first second =
      effectiveD8SmoothTensorPullbackField morphism tensor point second first
    rw [effectiveD8SmoothTensorPullbackField_apply,
      effectiveD8SmoothTensorPullbackField_apply]
    exact tensor.symmetric _ _ _

/-- Smooth tensor pullback by the identity is exact. -/
theorem effectiveD8SmoothSymmetricTensorPullback_refl
    (background : EffectiveD8Background)
    (tensor : SmoothSymmetricCovariantTwoTensor background.period
      background.period_ne_zero) :
    effectiveD8SmoothSymmetricTensorPullback
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) tensor = tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  exact effectiveD8CovariantTwoTensorPullbackFiberEquiv_refl
    background point (tensor.tensor point)

/-- Smooth tensor pullback is contravariantly functorial. -/
theorem effectiveD8SmoothSymmetricTensorPullback_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero) :
    effectiveD8SmoothSymmetricTensorPullback first
        (effectiveD8SmoothSymmetricTensorPullback second tensor) =
      effectiveD8SmoothSymmetricTensorPullback (first.trans second) tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  exact effectiveD8CovariantTwoTensorPullbackFiberEquiv_trans
    first second point (tensor.tensor (second (first point)))

/-- Smooth symmetric covariant two-tensors form a contravariant natural
section functor on the full nonzero-period effective D8 category. -/
def effectiveD8SmoothSymmetricTensorSectionFunctor :
    NaturalSectionFunctor effectiveD8BackgroundCategory where
  Section := fun background =>
    SmoothSymmetricCovariantTwoTensor background.period
      background.period_ne_zero
  pullback := fun morphism tensor =>
    effectiveD8SmoothSymmetricTensorPullback morphism.morphism tensor
  pullbackIdentity := by
    intro background tensor
    exact effectiveD8SmoothSymmetricTensorPullback_refl background tensor
  pullbackComposition := by
    intro source middle target secondMorphism firstMorphism tensor
    exact (effectiveD8SmoothSymmetricTensorPullback_trans
      firstMorphism.morphism secondMorphism.morphism tensor).symm

/-- Cross-background pullback of the musical equivalence. -/
def effectiveD8GeneralLorentzMetricPullbackMusical
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period
      target.period_ne_zero)
    (point : EffectiveQuotient source) :
    TangentFiber source point ≃L[Real] CotangentFiber source point :=
  (effectiveD8TangentFiberEquiv morphism point).trans
    ((metric.musical (morphism point)).trans
      (effectiveD8CotangentPullbackFiberEquiv morphism point))

@[simp] theorem effectiveD8GeneralLorentzMetricPullbackMusical_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period
      target.period_ne_zero)
    (point : EffectiveQuotient source)
    (first second : TangentFiber source point) :
    effectiveD8GeneralLorentzMetricPullbackMusical morphism metric point
        first second =
      metric.musical (morphism point)
        (effectiveD8TangentFiberEquiv morphism point first)
        (effectiveD8TangentFiberEquiv morphism point second) :=
  rfl

/-- Lorentz inertia `(3,1)` is preserved across arbitrary background
diffeomorphisms. -/
theorem effectiveD8CovariantTwoTensorPullbackFiberEquiv_lorentzian
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (point : EffectiveQuotient source)
    (tensor : EffectiveD8CovariantTwoTensorFiber target (morphism point))
    (hTensor : FiberIsLorentzian target.period target.period_ne_zero tensor) :
    FiberIsLorentzian source.period source.period_ne_zero
      (effectiveD8CovariantTwoTensorPullbackFiberEquiv morphism point
        tensor) := by
  rcases hTensor with ⟨frame, hFrame⟩
  refine ⟨(effectiveD8TangentFiberEquiv morphism point).trans frame, ?_⟩
  intro first second
  rw [effectiveD8CovariantTwoTensorPullbackFiberEquiv_apply, hFrame]
  rfl

/-- A general Lorentz metric is determined by its covariant tensor. -/
theorem effectiveD8SmoothGeneralLorentzMetric_ext
    (background : EffectiveD8Background)
    {first second : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero}
    (hTensor : first.tensor = second.tensor) : first = second := by
  cases first with
  | mk firstTensor firstMusical firstEq firstLorentzian =>
    cases second with
    | mk secondTensor secondMusical secondEq secondLorentzian =>
      dsimp at hTensor
      subst secondTensor
      have hMusical : firstMusical = secondMusical := by
        funext point
        apply ContinuousLinearEquiv.ext
        funext vector
        have hFirst := congrArg (fun current => current vector) (firstEq point)
        have hSecond := congrArg (fun current => current vector) (secondEq point)
        exact hFirst.trans hSecond.symm
      subst secondMusical
      rfl

/-- Genuine cross-background pullback of a smooth general Lorentz metric. -/
def effectiveD8SmoothGeneralLorentzMetricPullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period
      target.period_ne_zero) :
    SmoothGeneralLorentzMetric source.period source.period_ne_zero where
  tensor := effectiveD8SmoothSymmetricTensorPullback morphism metric.tensor
  musical := effectiveD8GeneralLorentzMetricPullbackMusical morphism metric
  musical_eq_tensor := by
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change metric.musical (morphism point)
        (effectiveD8TangentFiberEquiv morphism point first)
        (effectiveD8TangentFiberEquiv morphism point second) =
      effectiveD8SmoothTensorPullbackField morphism metric.tensor point
        first second
    rw [effectiveD8SmoothTensorPullbackField_apply,
      ← effectiveD8TangentFiberEquiv_apply,
      ← effectiveD8TangentFiberEquiv_apply]
    exact DFunLike.congr_fun
      (DFunLike.congr_fun (metric.musical_eq_tensor (morphism point)) _)
      _
  lorentzian := by
    intro point
    exact effectiveD8CovariantTwoTensorPullbackFiberEquiv_lorentzian
      morphism point (metric.tensor.tensor (morphism point))
      (metric.lorentzian (morphism point))

theorem effectiveD8SmoothGeneralLorentzMetricPullback_refl
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero) :
    effectiveD8SmoothGeneralLorentzMetricPullback
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) metric = metric := by
  apply effectiveD8SmoothGeneralLorentzMetric_ext background
  exact effectiveD8SmoothSymmetricTensorPullback_refl background metric.tensor

theorem effectiveD8SmoothGeneralLorentzMetricPullback_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (metric : SmoothGeneralLorentzMetric target.period
      target.period_ne_zero) :
    effectiveD8SmoothGeneralLorentzMetricPullback first
        (effectiveD8SmoothGeneralLorentzMetricPullback second metric) =
      effectiveD8SmoothGeneralLorentzMetricPullback (first.trans second)
        metric := by
  apply effectiveD8SmoothGeneralLorentzMetric_ext source
  exact effectiveD8SmoothSymmetricTensorPullback_trans
    first second metric.tensor

/-- Smooth general Lorentz metrics form a contravariant section functor on
the full effective-background category. -/
def effectiveD8SmoothGeneralLorentzMetricSectionFunctor :
    NaturalSectionFunctor effectiveD8BackgroundCategory where
  Section := fun background =>
    SmoothGeneralLorentzMetric background.period background.period_ne_zero
  pullback := fun morphism metric =>
    effectiveD8SmoothGeneralLorentzMetricPullback morphism.morphism metric
  pullbackIdentity := by
    intro background metric
    exact effectiveD8SmoothGeneralLorentzMetricPullback_refl background metric
  pullbackComposition := by
    intro source middle target secondMorphism firstMorphism metric
    exact (effectiveD8SmoothGeneralLorentzMetricPullback_trans
      firstMorphism.morphism secondMorphism.morphism metric).symm

/-! ## Locality of the natural pullbacks -/

/-- Tensor pullback at a source point depends only on the target tensor at its
image.  This is the pointwise locality statement for the natural operator. -/
theorem effectiveD8SmoothSymmetricTensorPullback_congr_at
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (first second : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (point : EffectiveQuotient source)
    (hTensor : first.tensor (morphism point) =
      second.tensor (morphism point)) :
    (effectiveD8SmoothSymmetricTensorPullback morphism first).tensor point =
      (effectiveD8SmoothSymmetricTensorPullback morphism second).tensor point := by
  change effectiveD8SmoothTensorPullbackField morphism first point =
    effectiveD8SmoothTensorPullbackField morphism second point
  unfold effectiveD8SmoothTensorPullbackField
  rw [hTensor]

/-- Sheaf locality: agreement of two target tensors on a set implies agreement
of their pullbacks on its inverse image. -/
theorem effectiveD8SmoothSymmetricTensorPullback_congr_on_preimage
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (first second : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (region : Set (EffectiveQuotient target))
    (hTensor : ∀ point ∈ region, first.tensor point = second.tensor point)
    (point : EffectiveQuotient source)
    (hPoint : morphism point ∈ region) :
    (effectiveD8SmoothSymmetricTensorPullback morphism first).tensor point =
      (effectiveD8SmoothSymmetricTensorPullback morphism second).tensor point :=
  effectiveD8SmoothSymmetricTensorPullback_congr_at morphism first second point
    (hTensor (morphism point) hPoint)

/-- The same locality law holds for the covariant tensors underlying general
Lorentz metrics. -/
theorem effectiveD8SmoothGeneralLorentzMetricPullback_congr_on_preimage
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (first second : SmoothGeneralLorentzMetric target.period
      target.period_ne_zero)
    (region : Set (EffectiveQuotient target))
    (hMetric : ∀ point ∈ region,
      first.tensor.tensor point = second.tensor.tensor point)
    (point : EffectiveQuotient source)
    (hPoint : morphism point ∈ region) :
    (effectiveD8SmoothGeneralLorentzMetricPullback morphism first).tensor.tensor
        point =
      (effectiveD8SmoothGeneralLorentzMetricPullback morphism second).tensor.tensor
        point :=
  effectiveD8SmoothSymmetricTensorPullback_congr_on_preimage morphism
    first.tensor second.tensor region hMetric point hPoint

end

end P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
end JanusFormal
