import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

/-!
# Intrinsic Lorentz tensor descent frontier

This gate extends the exact generator isometry of the intrinsic cover tensor
to every deck transformation and isolates the remaining dependent-section
descent to the smooth quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev QuotientTangent (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private theorem mfderiv_deck_add
    (first second : Int) (point : EffectiveCover period hPeriod) :
    mfderiv coverModelWithCorners coverModelWithCorners
        ((first + second) +ᵥ ·) point =
      (mfderiv coverModelWithCorners coverModelWithCorners
        (first +ᵥ ·) (second +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          (second +ᵥ ·) point) := by
  have hFirst : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (first +ᵥ ·) (second +ᵥ point) :=
    (reflectedSphereCover_deck_contMDiff period hPeriod first).mdifferentiableAt
      (by simp)
  have hSecond : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (second +ᵥ ·) point :=
    (reflectedSphereCover_deck_contMDiff period hPeriod second).mdifferentiableAt
      (by simp)
  calc
    _ = mfderiv coverModelWithCorners coverModelWithCorners
        ((first +ᵥ ·) ∘ (second +ᵥ ·)) point := by
      apply mfderiv_congr
      funext x
      exact add_vadd first second x
    _ = _ := mfderiv_comp point hFirst hSecond

/-- The intrinsic tensor is invariant under every genuine deck derivative,
not only under the chosen generator. -/
theorem intrinsicCoverLorentzTensor_deck_isometry
    (winding : Int) (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    intrinsicCoverLorentzTensor period hPeriod (winding +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  let motive : Int → Prop := fun winding =>
    intrinsicCoverLorentzTensor period hPeriod (winding +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second
  change motive winding
  refine Int.inductionOn' winding 0 ?_ (fun current _ ih => ?_)
      (fun current _ ih => ?_)
  · change intrinsicCoverLorentzTensor period hPeriod ((0 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((0 : Int) +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((0 : Int) +ᵥ ·) point second) = _
    have hZero : ((0 : Int) +ᵥ · : EffectiveCover period hPeriod →
        EffectiveCover period hPeriod) = id := by
      funext x
      simp
    rw [show (0 : Int) +ᵥ point = point by simp]
    rw [hZero, mfderiv_id]
    rfl
  · have hGenerator :=
      intrinsicCoverLorentzTensor_generator_isometry period hPeriod
        (current +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (current +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (current +ᵥ ·) point second)
    have hFirstDerivative := congrArg (fun derivative => derivative first)
      (mfderiv_deck_add period hPeriod 1 current point)
    have hSecondDerivative := congrArg (fun derivative => derivative second)
      (mfderiv_deck_add period hPeriod 1 current point)
    have hFirstDerivative' :
        mfderiv coverModelWithCorners coverModelWithCorners
            ((1 + current) +ᵥ ·) point first =
          mfderiv coverModelWithCorners coverModelWithCorners
            ((1 : Int) +ᵥ ·) (current +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                (current +ᵥ ·) point first) :=
      hFirstDerivative
    have hSecondDerivative' :
        mfderiv coverModelWithCorners coverModelWithCorners
            ((1 + current) +ᵥ ·) point second =
          mfderiv coverModelWithCorners coverModelWithCorners
            ((1 : Int) +ᵥ ·) (current +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                (current +ᵥ ·) point second) :=
      hSecondDerivative
    rw [← hFirstDerivative', ← hSecondDerivative'] at hGenerator
    rw [← add_vadd] at hGenerator
    have hStep : motive (current + 1) := by
      rw [show current + 1 = 1 + current by omega]
      exact hGenerator.trans ih
    exact hStep
  · have hGenerator :=
      intrinsicCoverLorentzTensor_generator_isometry period hPeriod
        ((current - 1) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((current - 1) +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((current - 1) +ᵥ ·) point second)
    have hFirstDerivative := congrArg (fun derivative => derivative first)
      (mfderiv_deck_add period hPeriod 1 (current - 1) point)
    have hSecondDerivative := congrArg (fun derivative => derivative second)
      (mfderiv_deck_add period hPeriod 1 (current - 1) point)
    have hFirstDerivative' :
        mfderiv coverModelWithCorners coverModelWithCorners
            ((1 + (current - 1)) +ᵥ ·) point first =
          mfderiv coverModelWithCorners coverModelWithCorners
            ((1 : Int) +ᵥ ·) ((current - 1) +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                ((current - 1) +ᵥ ·) point first) :=
      hFirstDerivative
    have hSecondDerivative' :
        mfderiv coverModelWithCorners coverModelWithCorners
            ((1 + (current - 1)) +ᵥ ·) point second =
          mfderiv coverModelWithCorners coverModelWithCorners
            ((1 : Int) +ᵥ ·) ((current - 1) +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                ((current - 1) +ᵥ ·) point second) :=
      hSecondDerivative
    rw [← hFirstDerivative', ← hSecondDerivative'] at hGenerator
    rw [← add_vadd] at hGenerator
    have hIndex : 1 + (current - 1) = current := by omega
    have ih' : motive (1 + (current - 1)) := by
      rw [hIndex]
      exact ih
    have hStep : motive (current - 1) := by
      exact hGenerator.symm.trans ih'
    exact hStep

/-- The derivative of the smooth quotient projection is a fiberwise
continuous linear equivalence. -/
def quotientProjectionDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point ≃L[Real]
      QuotientTangent period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) :=
  (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
theorem quotientProjectionDerivativeEquiv_coe
    (point : EffectiveCover period hPeriod) :
    (quotientProjectionDerivativeEquiv period hPeriod point :
      CoverTangent period hPeriod point →L[Real]
        QuotientTangent period hPeriod
          (mappingTorusMk (sphereData period hPeriod) point)) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod)) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point

/-- The canonical quotient-fiber tensor associated with one chosen cover
lift.  Both covariant arguments are transported by the inverse of the true
quotient-projection derivative. -/
def intrinsicQuotientTensorValueAtLift
    (point : EffectiveCover period hPeriod) :
    QuotientTangent period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) →L[Real]
      (QuotientTangent period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) →L[Real] Real) :=
  let derivative := quotientProjectionDerivativeEquiv period hPeriod point
  derivative.arrowCongr
    (derivative.arrowCongr (ContinuousLinearEquiv.refl Real Real))
    (intrinsicCoverLorentzTensor period hPeriod point)

/-- Pulling the quotient-fiber value back along the projection derivative
recovers the intrinsic cover tensor exactly. -/
theorem intrinsicQuotientTensorValueAtLift_pullback
    (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    intrinsicQuotientTensorValueAtLift period hPeriod point
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  let derivative := quotientProjectionDerivativeEquiv period hPeriod point
  have hDerivative (vector : CoverTangent period hPeriod point) :
      derivative vector =
        mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector := by
    exact DFunLike.congr_fun
      (quotientProjectionDerivativeEquiv_coe period hPeriod point) vector
  rw [← hDerivative first, ← hDerivative second]
  simp [intrinsicQuotientTensorValueAtLift, derivative]

/-- The actual quotient-fiber values constructed from deck-related lifts
agree on the corresponding projected tangent vectors. -/
theorem intrinsicQuotientTensorValueAtLift_deck_compatible
    (winding : Int) (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    intrinsicQuotientTensorValueAtLift period hPeriod (winding +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) (winding +ᵥ point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (winding +ᵥ ·) point first))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) (winding +ᵥ point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (winding +ᵥ ·) point second)) =
      intrinsicQuotientTensorValueAtLift period hPeriod point
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point second) := by
  rw [intrinsicQuotientTensorValueAtLift_pullback,
    intrinsicQuotientTensorValueAtLift_pullback]
  exact intrinsicCoverLorentzTensor_deck_isometry period hPeriod
    winding point first second

private abbrev QuotientTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  QuotientTangent period hPeriod point →L[Real]
    (QuotientTangent period hPeriod point →L[Real] Real)

/-- The lift-defined values glue to an honest dependent tensor field on the
quotient.  The heterogeneous quotient recursor records the changing tangent
fiber, while deck compatibility proves independence of the representative. -/
def intrinsicQuotientTensorField :
    ∀ point : EffectiveQuotient period hPeriod,
      QuotientTensorFiber period hPeriod point :=
  fun quotientPoint =>
    Quotient.hrecOn quotientPoint
      (intrinsicQuotientTensorValueAtLift period hPeriod)
      (fun firstPoint secondPoint hOrbit => by
        have hProjection :
            mappingTorusMk (sphereData period hPeriod) firstPoint =
              mappingTorusMk (sphereData period hPeriod) secondPoint :=
          Quotient.sound hOrbit
        obtain ⟨winding, hWinding⟩ :=
          (mappingTorusMk_eq_iff_exists_vadd
            (sphereData period hPeriod) firstPoint secondPoint).1 hProjection
        subst firstPoint
        clear hOrbit
        have hTangent :
            QuotientTangent period hPeriod
                (mappingTorusMk (sphereData period hPeriod)
                  (winding +ᵥ secondPoint)) =
              QuotientTangent period hPeriod
                (mappingTorusMk (sphereData period hPeriod) secondPoint) :=
          congrArg (QuotientTangent period hPeriod) hProjection
        cases hTangent
        apply heq_of_eq
        apply ContinuousLinearMap.ext
        intro firstVector
        apply ContinuousLinearMap.ext
        intro secondVector
        let derivative := quotientProjectionDerivativeEquiv period hPeriod secondPoint
        obtain ⟨firstPreimage, rfl⟩ := derivative.surjective firstVector
        obtain ⟨secondPreimage, rfl⟩ := derivative.surjective secondVector
        have hDerivative (vector : CoverTangent period hPeriod secondPoint) :
            derivative vector =
              mfderiv coverModelWithCorners coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod)) secondPoint vector := by
          exact DFunLike.congr_fun
            (quotientProjectionDerivativeEquiv_coe period hPeriod secondPoint) vector
        have hNatural (vector : CoverTangent period hPeriod secondPoint) :
            mfderiv coverModelWithCorners coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod))
                (winding +ᵥ secondPoint)
                (mfderiv coverModelWithCorners coverModelWithCorners
                  (winding +ᵥ ·) secondPoint vector) =
              mfderiv coverModelWithCorners coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod)) secondPoint vector := by
          have hProjectionAt : MDifferentiableAt coverModelWithCorners
              coverModelWithCorners
              (mappingTorusMk (sphereData period hPeriod))
              (winding +ᵥ secondPoint) :=
            (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
              |>.mdifferentiableAt (by simp)
          have hDeckAt : MDifferentiableAt coverModelWithCorners
              coverModelWithCorners (winding +ᵥ ·) secondPoint :=
            (reflectedSphereCover_deck_contMDiff period hPeriod winding)
              |>.mdifferentiableAt (by simp)
          have hComposite := mfderiv_comp secondPoint hProjectionAt hDeckAt
          have hMap :
              (mappingTorusMk (sphereData period hPeriod)) ∘ (winding +ᵥ ·) =
                mappingTorusMk (sphereData period hPeriod) := by
            funext point
            exact (mappingTorusMk_eq_iff_exists_vadd
              (sphereData period hPeriod) _ _).2 ⟨winding, rfl⟩
          calc
            _ = mfderiv coverModelWithCorners coverModelWithCorners
                  ((mappingTorusMk (sphereData period hPeriod)) ∘
                    (winding +ᵥ ·)) secondPoint vector := by
              rw [hComposite]
              rfl
            _ = _ := by rw [hMap]
        have hCompatibility :=
          intrinsicQuotientTensorValueAtLift_deck_compatible period hPeriod
            winding secondPoint firstPreimage secondPreimage
        rw [hNatural, hNatural] at hCompatibility
        rw [hDerivative, hDerivative]
        exact hCompatibility)

@[simp]
theorem intrinsicQuotientTensorField_mk
    (point : EffectiveCover period hPeriod) :
    intrinsicQuotientTensorField period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) =
      intrinsicQuotientTensorValueAtLift period hPeriod point :=
  rfl

/-- Pullback of the glued dependent field is exactly the intrinsic cover
tensor. -/
theorem intrinsicQuotientTensorField_pullback
    (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    intrinsicQuotientTensorField period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  rw [intrinsicQuotientTensorField_mk,
    intrinsicQuotientTensorValueAtLift_pullback]

private abbrev CoverTensorFiber
    (point : EffectiveCover period hPeriod) :=
  CoverTangent period hPeriod point →L[Real]
    (CoverTangent period hPeriod point →L[Real] Real)

private abbrev ModelCovector := CoverCoordinates →L[Real] Real

private abbrev ModelTensor := CoverCoordinates →L[Real] ModelCovector

/-- Pullback of a model tensor through a model linear map. -/
private def pullbackModelTensor
    (derivative : CoverCoordinates →L[Real] CoverCoordinates)
    (tensor : ModelTensor) : ModelTensor :=
  (derivative.precomp Real).comp (tensor.comp derivative)

/-- Local expression of the quotient tensor obtained by pulling the cover
tensor back through a local inverse of the quotient projection. -/
private def localInversePullbackTensor
    (localInverse : EffectiveQuotient period hPeriod →
      EffectiveCover period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    QuotientTensorFiber period hPeriod point :=
  let derivative := mfderiv coverModelWithCorners coverModelWithCorners
    localInverse point
  (derivative.precomp Real).comp
    ((intrinsicCoverLorentzTensor period hPeriod (localInverse point)).comp
      derivative)

/-- Pulling a smooth cover tensor through a smooth local inverse gives a
smooth quotient-tensor section at the base point. -/
private theorem localInversePullbackTensor_contMDiffAt
    (localInverse : EffectiveQuotient period hPeriod →
      EffectiveCover period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hLocalInverse : ContMDiffAt coverModelWithCorners
      coverModelWithCorners ∞ localInverse point) :
    ContMDiffAt coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, ModelTensor)) ∞
      (fun current => Bundle.TotalSpace.mk' ModelTensor current
        (localInversePullbackTensor period hPeriod localInverse current)) point := by
  rw [contMDiffAt_section]
  have hCoverCoordinates :=
    (intrinsicCoverLorentzTensor period hPeriod).contMDiff
      (localInverse point)
  rw [contMDiffAt_section] at hCoverCoordinates
  have hCoverCoordinates := hCoverCoordinates.comp point hLocalInverse
  have hDerivative : ContMDiffAt coverModelWithCorners
      𝓘(Real, CoverCoordinates →L[Real] CoverCoordinates) ∞
      (inTangentCoordinates coverModelWithCorners coverModelWithCorners
        id localInverse
        (mfderiv coverModelWithCorners coverModelWithCorners localInverse)
        point) point :=
    hLocalInverse.mfderiv_const (m := ∞) (n := ∞) (by simp)
  have hPullback : ContMDiffAt coverModelWithCorners
      𝓘(Real, ModelTensor) ∞
      (fun current => pullbackModelTensor
        (inTangentCoordinates coverModelWithCorners coverModelWithCorners
          id localInverse
          (mfderiv coverModelWithCorners coverModelWithCorners localInverse)
          point current)
        ((trivializationAt ModelTensor (CoverTensorFiber period hPeriod)
          (localInverse point)
          ⟨localInverse current,
            intrinsicCoverLorentzTensor period hPeriod
              (localInverse current)⟩).2)) point := by
    exact (hDerivative.clm_precomp (F₃ := Real)).clm_comp
      (hCoverCoordinates.clm_comp hDerivative)
  apply hPullback.congr_of_eventuallyEq
  have hQuotientBase :
      (trivializationAt CoverCoordinates
        (QuotientTangent period hPeriod) point).baseSet ∈ nhds point :=
    (trivializationAt CoverCoordinates
      (QuotientTangent period hPeriod) point).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' point)
  have hCoverBase : localInverse ⁻¹'
      (trivializationAt CoverCoordinates
        (CoverTangent period hPeriod) (localInverse point)).baseSet ∈ nhds point :=
    hLocalInverse.continuousAt.preimage_mem_nhds
      ((trivializationAt CoverCoordinates
        (CoverTangent period hPeriod) (localInverse point)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (localInverse point)))
  filter_upwards [hQuotientBase, hCoverBase] with current hCurrent hLocalCurrent
  have hCurrent' : current ∈ (chartAt CoverModel point).source := by
    simpa only [QuotientTangent, TangentBundle.trivializationAt_baseSet] using
      hCurrent
  change localInverse current ∈
    (trivializationAt CoverCoordinates
      (CoverTangent period hPeriod) (localInverse point)).baseSet at hLocalCurrent
  have hLocalCurrent' : localInverse current ∈
      (chartAt CoverModel (localInverse point)).source := by
    simpa only [CoverTangent, TangentBundle.trivializationAt_baseSet] using
      hLocalCurrent
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp [localInversePullbackTensor, pullbackModelTensor,
    inTangentCoordinates, hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates,
    Trivialization.linearMapAt_apply, Trivialization.symmL_apply,
    TangentBundle.trivializationAt_baseSet,
    Bundle.Trivial.trivialization_baseSet, hom_trivializationAt_baseSet,
    hCurrent', hLocalCurrent']

/-- On the source of a quotient local inverse, its pullback expression is
the lift-independent quotient field. -/
private theorem localInversePullbackTensor_eq_intrinsicQuotientTensorField
    (anchor : EffectiveCover period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈
      (reflectedSphere_projection_isLocalDiffeomorph period hPeriod anchor).localInverse.source) :
    localInversePullbackTensor period hPeriod
        (reflectedSphere_projection_isLocalDiffeomorph period hPeriod anchor).localInverse point =
      intrinsicQuotientTensorField period hPeriod point := by
  let hAt := reflectedSphere_projection_isLocalDiffeomorph
    period hPeriod anchor
  let localInverse := hAt.localInverse
  let projection := mappingTorusMk (sphereData period hPeriod)
  let fieldModel : EffectiveQuotient period hPeriod → ModelTensor :=
    fun current => intrinsicQuotientTensorField period hPeriod current
  have hRight : projection (localInverse point) = point :=
    hAt.localInverse_right_inv hPoint
  have hField :
      fieldModel (projection (localInverse point)) = fieldModel point :=
    congrArg fieldModel hRight
  change localInversePullbackTensor period hPeriod localInverse point =
    fieldModel point
  rw [← hField]
  change localInversePullbackTensor period hPeriod localInverse point =
    intrinsicQuotientTensorField period hPeriod
      (projection (localInverse point))
  rw [intrinsicQuotientTensorField_mk]
  have hLocalSmoothAt : ContMDiffAt coverModelWithCorners
      coverModelWithCorners ∞ localInverse point :=
    (hAt.localInverse.contMDiffOn_toFun.contMDiffAt
      (hAt.localInverse.open_source.mem_nhds hPoint)).of_le (by simp)
  have hLocalAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners localInverse point :=
    hLocalSmoothAt.mdifferentiableAt (by simp)
  have hProjectionAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners projection (localInverse point) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hEventually : projection ∘ localInverse =ᶠ[nhds point] id :=
    Filter.eventually_of_mem
      (hAt.localInverse.open_source.mem_nhds hPoint)
      hAt.localInverse_eqOn_right
  have hInverse (vector : QuotientTangent period hPeriod point) :
      mfderiv coverModelWithCorners coverModelWithCorners projection
          (localInverse point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            localInverse point vector) = vector := by
    have hMaps :
        (mfderiv coverModelWithCorners coverModelWithCorners projection
          (localInverse point)).comp
            (mfderiv coverModelWithCorners coverModelWithCorners
              localInverse point) =
          ContinuousLinearMap.id Real
            (QuotientTangent period hPeriod point) := by
      rw [← mfderiv_id, ← hEventually.mfderiv_eq]
      exact (mfderiv_comp point hProjectionAt hLocalAt).symm
    exact DFunLike.congr_fun hMaps vector
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change intrinsicCoverLorentzTensor period hPeriod (localInverse point)
      (mfderiv coverModelWithCorners coverModelWithCorners
        localInverse point first)
      (mfderiv coverModelWithCorners coverModelWithCorners
        localInverse point second) = _
  rw [← intrinsicQuotientTensorValueAtLift_pullback period hPeriod
    (localInverse point)
    (mfderiv coverModelWithCorners coverModelWithCorners
      localInverse point first)
    (mfderiv coverModelWithCorners coverModelWithCorners
      localInverse point second), hInverse, hInverse]
  rfl

/-- The lift-independent quotient field is a genuine globally smooth
covariant two-tensor section. -/
def intrinsicQuotientTensorSection :
    SmoothCovariantTwoTensor period hPeriod where
  toFun := intrinsicQuotientTensorField period hPeriod
  contMDiff_toFun := by
    intro quotientPoint
    obtain ⟨anchor, rfl⟩ :=
      mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
    let hAt := reflectedSphere_projection_isLocalDiffeomorph
      period hPeriod anchor
    have hLocalInverse : ContMDiffAt coverModelWithCorners
        coverModelWithCorners ∞ hAt.localInverse
        (mappingTorusMk (sphereData period hPeriod) anchor) :=
      hAt.localInverse_contMDiffAt.of_le (by simp)
    have hLocalSmooth :=
      localInversePullbackTensor_contMDiffAt period hPeriod
        hAt.localInverse
        (mappingTorusMk (sphereData period hPeriod) anchor) hLocalInverse
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [hAt.localInverse.open_source.mem_nhds
      hAt.localInverse_mem_source] with point hPoint
    rw [localInversePullbackTensor_eq_intrinsicQuotientTensorField
      period hPeriod anchor point hPoint]

/-- Exact remaining dependent-section descent datum.  Its pullback equation
uses the true derivative of the quotient projection. -/
structure IntrinsicTensorQuotientDescent where
  tensor : SmoothCovariantTwoTensor period hPeriod
  pullback : ∀ (point : EffectiveCover period hPeriod)
      (first second : CoverTangent period hPeriod point),
    tensor (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second

/-- The canonical smooth quotient descent of the intrinsic cover tensor. -/
def intrinsicTensorQuotientDescent :
    IntrinsicTensorQuotientDescent period hPeriod where
  tensor := intrinsicQuotientTensorSection period hPeriod
  pullback := intrinsicQuotientTensorField_pullback period hPeriod

/-- A descended intrinsic tensor is unique because the quotient projection
and each of its tangent derivatives are surjective. -/
theorem IntrinsicTensorQuotientDescent.tensor_unique
    (first second : IntrinsicTensorQuotientDescent period hPeriod) :
    first.tensor = second.tensor := by
  apply ContMDiffSection.ext
  intro quotientPoint
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  apply ContinuousLinearMap.ext
  intro firstVector
  apply ContinuousLinearMap.ext
  intro secondVector
  let derivative := quotientProjectionDerivativeEquiv period hPeriod point
  obtain ⟨firstPreimage, rfl⟩ := derivative.surjective firstVector
  obtain ⟨secondPreimage, rfl⟩ := derivative.surjective secondVector
  have hDerivative (vector : CoverTangent period hPeriod point) :
      derivative vector =
        mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector := by
    exact DFunLike.congr_fun
      (quotientProjectionDerivativeEquiv_coe period hPeriod point) vector
  rw [hDerivative, hDerivative, first.pullback, second.pullback]

/-- The unique descended tensor is symmetric. -/
def IntrinsicTensorQuotientDescent.toSymmetricTensor
    (descent : IntrinsicTensorQuotientDescent period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := descent.tensor
  symmetric := by
    intro quotientPoint firstVector secondVector
    obtain ⟨point, rfl⟩ :=
      mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
    let derivative := quotientProjectionDerivativeEquiv period hPeriod point
    obtain ⟨firstPreimage, rfl⟩ := derivative.surjective firstVector
    obtain ⟨secondPreimage, rfl⟩ := derivative.surjective secondVector
    have hDerivative (vector : CoverTangent period hPeriod point) :
        derivative vector =
          mfderiv coverModelWithCorners coverModelWithCorners
            (mappingTorusMk (sphereData period hPeriod)) point vector := by
      exact DFunLike.congr_fun
        (quotientProjectionDerivativeEquiv_coe period hPeriod point) vector
    rw [hDerivative, hDerivative, descent.pullback, descent.pullback]
    exact intrinsicCoverLorentzTensor_symmetric period hPeriod point _ _

/-- Independent fiber certificate still required to upgrade the descended
symmetric tensor to a genuine Lorentz metric. -/
structure IntrinsicCoverLorentzCertificate where
  frame : ∀ point : EffectiveCover period hPeriod,
    CoverTangent period hPeriod point ≃L[Real] CoverCoordinates
  tensor_eq_model : ∀ (point : EffectiveCover period hPeriod)
      (first second : CoverTangent period hPeriod point),
    intrinsicCoverLorentzTensor period hPeriod point first second =
      modelMinkowskiPair (frame point first) (frame point second)

/-- Any pointwise Lorentz certificate on the cover transports through the
quotient-projection derivative to the canonical descended tensor. -/
theorem IntrinsicCoverLorentzCertificate.quotient_lorentzian
    (certificate : IntrinsicCoverLorentzCertificate period hPeriod) :
    IsEverywhereLorentzian period hPeriod
      (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor := by
  intro quotientPoint
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  let derivative := quotientProjectionDerivativeEquiv period hPeriod point
  refine ⟨derivative.symm.trans (certificate.frame point), ?_⟩
  intro firstVector secondVector
  obtain ⟨firstPreimage, rfl⟩ := derivative.surjective firstVector
  obtain ⟨secondPreimage, rfl⟩ := derivative.surjective secondVector
  have hDerivative (vector : CoverTangent period hPeriod point) :
      derivative vector =
        mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector := by
    exact DFunLike.congr_fun
      (quotientProjectionDerivativeEquiv_coe period hPeriod point) vector
  change (intrinsicTensorQuotientDescent period hPeriod).tensor
      (mappingTorusMk (sphereData period hPeriod) point)
      (derivative firstPreimage) (derivative secondPreimage) = _
  calc
    _ = intrinsicCoverLorentzTensor period hPeriod point
        firstPreimage secondPreimage := by
      rw [hDerivative, hDerivative]
      exact (intrinsicTensorQuotientDescent period hPeriod).pullback
        point firstPreimage secondPreimage
    _ = modelMinkowskiPair (certificate.frame point firstPreimage)
        (certificate.frame point secondPreimage) :=
      certificate.tensor_eq_model point firstPreimage secondPreimage
    _ = _ := by simp [derivative]

end

end P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
end JanusFormal
