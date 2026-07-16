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

end

end P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
end JanusFormal
