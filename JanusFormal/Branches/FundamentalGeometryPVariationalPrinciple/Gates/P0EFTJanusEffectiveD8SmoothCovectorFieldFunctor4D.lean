import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8NaturalTangentBundle4D

/-!
# Smooth covector fields on the global effective D8 category

The fiberwise cotangent pullback is promoted to genuine smooth one-form
sections between arbitrary nonzero-period effective backgrounds, with exact
identity, composition and locality laws.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
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

private abbrev CovectorModel := CoverCoordinates →L[Real] Real

/-- Genuine smooth one-form sections on an effective D8 background. -/
abbrev EffectiveD8SmoothCovectorField (background : EffectiveD8Background) :=
  ContMDiffSection coverModelWithCorners CovectorModel ∞
    (CotangentFiber background)

/-- Fiberwise pullback of a smooth target covector field. -/
def effectiveD8SmoothCovectorPullbackField
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target) :
    ∀ point : EffectiveQuotient source, CotangentFiber source point :=
  fun point => effectiveD8CotangentPullbackFiberEquiv morphism point
    (field (morphism point))

@[simp] theorem effectiveD8SmoothCovectorPullbackField_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target)
    (point : EffectiveQuotient source)
    (tangent : TangentFiber source point) :
    effectiveD8SmoothCovectorPullbackField morphism field point tangent =
      field (morphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners morphism point
          tangent) := by
  unfold effectiveD8SmoothCovectorPullbackField
  rw [effectiveD8CotangentPullbackFiberEquiv_apply,
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

private def covectorCoordinates
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target)
    (point current : EffectiveQuotient source) : CovectorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber target)
    Real (fun _ : EffectiveQuotient target => Real)
    (morphism point) (morphism current) (morphism point) (morphism current)
    (field (morphism current))

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
        (mfderiv coverModelWithCorners coverModelWithCorners morphism current)
      by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private def pullbackCovectorCoordinates
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target)
    (point current : EffectiveQuotient source) : CovectorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber source)
    Real (fun _ : EffectiveQuotient source => Real)
    point current point current
    (effectiveD8SmoothCovectorPullbackField morphism field current)

private theorem pullbackCovectorCoordinates_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target)
    (point current : EffectiveQuotient source)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber source) point).baseSet)
    (vector : CoverCoordinates) :
    pullbackCovectorCoordinates morphism field point current vector =
      effectiveD8SmoothCovectorPullbackField morphism field current
        ((trivializationAt CoverCoordinates (TangentFiber source) point).symm
          current vector) := by
  rw [show pullbackCovectorCoordinates morphism field point current =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber source)
        Real (fun _ : EffectiveQuotient source => Real)
        point current point current
        (effectiveD8SmoothCovectorPullbackField morphism field current) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent (by simp)]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply]

private theorem covectorCoordinates_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target)
    (point current : EffectiveQuotient source)
    (hImage : morphism current ∈
      (trivializationAt CoverCoordinates (TangentFiber target)
        (morphism point)).baseSet)
    (vector : CoverCoordinates) :
    covectorCoordinates morphism field point current vector =
      field (morphism current)
        ((trivializationAt CoverCoordinates (TangentFiber target)
          (morphism point)).symm (morphism current) vector) := by
  rw [show covectorCoordinates morphism field point current =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber target)
        Real (fun _ : EffectiveQuotient target => Real)
        (morphism point) (morphism current) (morphism point) (morphism current)
        (field (morphism current)) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hImage (by simp)]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply]

private theorem pullbackCovectorCoordinates_eq
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target)
    (point current : EffectiveQuotient source)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber source) point).baseSet)
    (hImage : morphism current ∈
      (trivializationAt CoverCoordinates (TangentFiber target)
        (morphism point)).baseSet) :
    pullbackCovectorCoordinates morphism field point current =
      (covectorCoordinates morphism field point current).comp
        (derivativeCoordinates morphism point current) := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [pullbackCovectorCoordinates_apply morphism field point current hCurrent]
  simp only [ContinuousLinearMap.comp_apply,
    effectiveD8SmoothCovectorPullbackField_apply]
  rw [covectorCoordinates_apply morphism field point current hImage]
  rw [derivativeCoordinates_apply morphism point current hCurrent hImage vector]
  simp only [Trivialization.symm_linearMapAt _ hImage]

/-- Pullback of a smooth target one-form is a smooth source one-form. -/
theorem effectiveD8SmoothCovectorPullbackField_contMDiff
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target) :
    ContMDiff coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, CovectorModel)) ∞
      (fun point => TotalSpace.mk' CovectorModel
        (E := CotangentFiber source) point
        (effectiveD8SmoothCovectorPullbackField morphism field point)) := by
  intro point
  have hD := morphism.contMDiff.contMDiffAt.mfderiv_const
    (x₀ := point) (m := ∞) (by simp)
  have hMap := morphism.contMDiff.of_le (m := ∞) (by simp)
  have hField := field.contMDiff.comp hMap
  have hFieldAt := hField point
  rw [contMDiffAt_hom_bundle] at hFieldAt
  have hFormula := hFieldAt.2.clm_comp hD
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
  simpa only [pullbackCovectorCoordinates, covectorCoordinates,
    derivativeCoordinates, Function.comp_apply] using
      (pullbackCovectorCoordinates_eq morphism field point current
        hCurrent' hImage')

/-- Genuine smooth one-form pullback. -/
def effectiveD8SmoothCovectorFieldPullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothCovectorField target) :
    EffectiveD8SmoothCovectorField source where
  toFun := effectiveD8SmoothCovectorPullbackField morphism field
  contMDiff_toFun := effectiveD8SmoothCovectorPullbackField_contMDiff
    morphism field

theorem effectiveD8SmoothCovectorFieldPullback_refl
    (background : EffectiveD8Background)
    (field : EffectiveD8SmoothCovectorField background) :
    effectiveD8SmoothCovectorFieldPullback
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) field = field := by
  apply ContMDiffSection.ext
  intro point
  exact effectiveD8CotangentPullbackFiberEquiv_refl
    background point (field point)

theorem effectiveD8SmoothCovectorFieldPullback_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (field : EffectiveD8SmoothCovectorField target) :
    effectiveD8SmoothCovectorFieldPullback first
        (effectiveD8SmoothCovectorFieldPullback second field) =
      effectiveD8SmoothCovectorFieldPullback (first.trans second) field := by
  apply ContMDiffSection.ext
  intro point
  exact effectiveD8CotangentPullbackFiberEquiv_trans first second point
    (field (second (first point)))

theorem effectiveD8SmoothCovectorFieldPullback_congr_on_preimage
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (first second : EffectiveD8SmoothCovectorField target)
    (region : Set (EffectiveQuotient target))
    (hField : ∀ point ∈ region, first point = second point)
    (point : EffectiveQuotient source)
    (hPoint : morphism point ∈ region) :
    effectiveD8SmoothCovectorFieldPullback morphism first point =
      effectiveD8SmoothCovectorFieldPullback morphism second point := by
  change effectiveD8CotangentPullbackFiberEquiv morphism point
      (first (morphism point)) =
    effectiveD8CotangentPullbackFiberEquiv morphism point
      (second (morphism point))
  rw [hField (morphism point) hPoint]

/-- Smooth one-forms form a contravariant natural section functor. -/
def effectiveD8SmoothCovectorFieldSectionFunctor :
    NaturalSectionFunctor effectiveD8BackgroundCategory where
  Section := EffectiveD8SmoothCovectorField
  pullback := fun morphism field =>
    effectiveD8SmoothCovectorFieldPullback morphism.morphism field
  pullbackIdentity := by
    intro background field
    exact effectiveD8SmoothCovectorFieldPullback_refl background field
  pullbackComposition := by
    intro source middle target secondMorphism firstMorphism field
    exact (effectiveD8SmoothCovectorFieldPullback_trans
      firstMorphism.morphism secondMorphism.morphism field).symm

end

end P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
end JanusFormal
