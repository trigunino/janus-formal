import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackGlobalLorentz4D

/-!
# Smooth ambient tensor pullback to the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance quotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

private abbrev AmbientTangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev AmbientCotangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  AmbientTangentFiber period hPeriod point →L[Real] Real

private abbrev AmbientCovariantTwoTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  AmbientTangentFiber period hPeriod point →L[Real]
    AmbientCotangentFiber period hPeriod point

private abbrev AmbientCovariantTwoTensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

private abbrev CutBulkCovariantTwoTensorModel :=
  CutCollarCoordinates →L[Real] CutCollarCoordinates →L[Real] Real

/-- Genuine smooth covariant rank-two tensor fields on the cut bulk. -/
abbrev CutBulkSmoothCovariantTwoTensor :=
  ContMDiffSection cutCollarModelWithCorners CutBulkCovariantTwoTensorModel ∞
    (CutBulkCovariantTwoTensorFiber period hPeriod)

/-- Smooth symmetric covariant rank-two tensor fields on the cut bulk. -/
structure CutBulkSmoothSymmetricCovariantTwoTensor where
  tensor : CutBulkSmoothCovariantTwoTensor period hPeriod
  symmetric : ∀ point first second,
    tensor point first second = tensor point second first

private def derivativeCoordinates
    (point current : PositiveHemisphereCutBulk period hPeriod) :
    CutCollarCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates cutCollarModelWithCorners coverModelWithCorners
    id (cutBulkToAmbient period hPeriod)
    (mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod)) point current

private def tensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : PositiveHemisphereCutBulk period hPeriod) :
    AmbientCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates
    (AmbientTangentFiber period hPeriod)
    (CoverCoordinates →L[Real] Real)
    (AmbientCotangentFiber period hPeriod)
    (cutBulkToAmbient period hPeriod point)
    (cutBulkToAmbient period hPeriod current)
    (cutBulkToAmbient period hPeriod point)
    (cutBulkToAmbient period hPeriod current)
    (tensor.tensor (cutBulkToAmbient period hPeriod current))

private def pullbackTensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : PositiveHemisphereCutBulk period hPeriod) :
    CutBulkCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CutCollarCoordinates
    (CutBulkTangentFiber period hPeriod)
    (CutCollarCoordinates →L[Real] Real)
    (fun current => CutBulkTangentFiber period hPeriod current →L[Real] Real)
    point current point current
    (cutBulkAmbientTensorPullback period hPeriod tensor.tensor.toTensorField current)

private def coordinatePullback
    (derivative : CutCollarCoordinates →L[Real] CoverCoordinates)
    (tensor : AmbientCovariantTwoTensorModel) :
    CutBulkCovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem derivativeCoordinates_apply
    (point current : PositiveHemisphereCutBulk period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CutCollarCoordinates
        (CutBulkTangentFiber period hPeriod) point).baseSet)
    (hImage : cutBulkToAmbient period hPeriod current ∈
      (trivializationAt CoverCoordinates
        (AmbientTangentFiber period hPeriod)
        (cutBulkToAmbient period hPeriod point)).baseSet)
    (vector : CutCollarCoordinates) :
    derivativeCoordinates period hPeriod point current vector =
      (trivializationAt CoverCoordinates
        (AmbientTangentFiber period hPeriod)
        (cutBulkToAmbient period hPeriod point)).linearMapAt Real
          (cutBulkToAmbient period hPeriod current)
          (mfderiv cutCollarModelWithCorners coverModelWithCorners
            (cutBulkToAmbient period hPeriod) current
            ((trivializationAt CutCollarCoordinates
              (CutBulkTangentFiber period hPeriod) point).symm
                current vector)) := by
  rw [show derivativeCoordinates period hPeriod point current =
      ContinuousLinearMap.inCoordinates CutCollarCoordinates
        (CutBulkTangentFiber period hPeriod)
        CoverCoordinates (AmbientTangentFiber period hPeriod)
        point current
        (cutBulkToAmbient period hPeriod point)
        (cutBulkToAmbient period hPeriod current)
        (mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkToAmbient period hPeriod) current) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem pullbackTensorCoordinates_eq
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : PositiveHemisphereCutBulk period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CutCollarCoordinates
        (CutBulkTangentFiber period hPeriod) point).baseSet)
    (hImage : cutBulkToAmbient period hPeriod current ∈
      (trivializationAt CoverCoordinates
        (AmbientTangentFiber period hPeriod)
        (cutBulkToAmbient period hPeriod point)).baseSet) :
    pullbackTensorCoordinates period hPeriod tensor point current =
      coordinatePullback
        (derivativeCoordinates period hPeriod point current)
        (tensorCoordinates period hPeriod tensor point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show pullbackTensorCoordinates period hPeriod tensor point current
        first second =
      ContinuousLinearMap.inCoordinates CutCollarCoordinates
        (CutBulkTangentFiber period hPeriod)
        (CutCollarCoordinates →L[Real] Real)
        (fun current => CutBulkTangentFiber period hPeriod current →L[Real] Real)
        point current point current
        (cutBulkAmbientTensorPullback period hPeriod
          tensor.tensor.toTensorField current) first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [cutBulkAmbientTensorPullback_apply, coordinatePullback,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  rw [show tensorCoordinates period hPeriod tensor point current
        (derivativeCoordinates period hPeriod point current first)
        (derivativeCoordinates period hPeriod point current second) =
      ContinuousLinearMap.inCoordinates CoverCoordinates
        (AmbientTangentFiber period hPeriod)
        (CoverCoordinates →L[Real] Real)
        (AmbientCotangentFiber period hPeriod)
        (cutBulkToAmbient period hPeriod point)
        (cutBulkToAmbient period hPeriod current)
        (cutBulkToAmbient period hPeriod point)
        (cutBulkToAmbient period hPeriod current)
        (tensor.tensor (cutBulkToAmbient period hPeriod current))
        (derivativeCoordinates period hPeriod point current first)
        (derivativeCoordinates period hPeriod point current second) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [derivativeCoordinates_apply period hPeriod point current
      hCurrent hImage first,
    derivativeCoordinates_apply period hPeriod point current
      hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

/-- Pullback of a smooth ambient tensor is a smooth cut-bulk section. -/
theorem cutBulkAmbientTensorPullback_contMDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff cutCollarModelWithCorners
      (cutCollarModelWithCorners.prod
        𝓘(Real, CutBulkCovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' CutBulkCovariantTwoTensorModel
        (E := CutBulkCovariantTwoTensorFiber period hPeriod) point
        (cutBulkAmbientTensorPullback period hPeriod
          tensor.tensor.toTensorField point)) := by
  intro point
  have hD := (cutBulkToAmbient_contMDiff period hPeriod).contMDiffAt.mfderiv_const
    (x₀ := point) (m := ∞) (by simp)
  have hMap := (cutBulkToAmbient_contMDiff period hPeriod).of_le
    (m := ∞) (by simp)
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
      current ∈ (trivializationAt CutCollarCoordinates
        (CutBulkTangentFiber period hPeriod) point).baseSet :=
    (trivializationAt CutCollarCoordinates
      (CutBulkTangentFiber period hPeriod) point).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt CutCollarCoordinates
          (CutBulkTangentFiber period hPeriod) point)
  have hImage : ∀ᶠ current in 𝓝 point,
      cutBulkToAmbient period hPeriod current ∈
        (trivializationAt CoverCoordinates
          (AmbientTangentFiber period hPeriod)
          (cutBulkToAmbient period hPeriod point)).baseSet :=
    (cutBulkToAmbient_contMDiff period hPeriod).continuous.continuousAt
      ((trivializationAt CoverCoordinates
        (AmbientTangentFiber period hPeriod)
        (cutBulkToAmbient period hPeriod point)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates
            (AmbientTangentFiber period hPeriod)
            (cutBulkToAmbient period hPeriod point)))
  filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
  simpa only [pullbackTensorCoordinates, coordinatePullback,
    derivativeCoordinates, tensorCoordinates, Function.comp_apply] using
      (pullbackTensorCoordinates_eq period hPeriod tensor point current
        hCurrent' hImage')

/-- Genuine smooth symmetric pullback of an ambient tensor. -/
def cutBulkAmbientSmoothTensorPullback
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    CutBulkSmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := cutBulkAmbientTensorPullback period hPeriod
        tensor.tensor.toTensorField
      contMDiff_toFun :=
        cutBulkAmbientTensorPullback_contMDiff period hPeriod tensor }
  symmetric := by
    intro point first second
    exact cutBulkAmbientTensorPullback_symmetric period hPeriod
      tensor.tensor.toTensorField tensor.symmetric point first second

end
end P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D
end JanusFormal
