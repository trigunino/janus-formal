import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D

/-!
# Unconditional smoothness of the general Lorentz-tensor PT pullback

This gate discharges the local dependent-Hom regularity contract by working
in the tangent and iterated Hom-bundle trivializations.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle
open Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev CovariantTwoTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real]
    CotangentFiber period hPeriod point

private abbrev CovariantTwoTensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

private def ptDerivativeCoordinates
    (point current : EffectiveQuotient period hPeriod) :
    CoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates coverModelWithCorners coverModelWithCorners
    id (reflectedSpherePT period hPeriod)
    (mfderiv coverModelWithCorners coverModelWithCorners
      (reflectedSpherePT period hPeriod)) point current

private def ptTensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveQuotient period hPeriod) :
    CovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
    (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
    (reflectedSpherePT period hPeriod point)
    (reflectedSpherePT period hPeriod current)
    (reflectedSpherePT period hPeriod point)
    (reflectedSpherePT period hPeriod current)
    (tensor.tensor (reflectedSpherePT period hPeriod current))

private def ptPullbackTensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveQuotient period hPeriod) :
    CovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
    (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
    point current point current
    (ptTensorPullback period hPeriod tensor.tensor.toTensorField current)

private def coordinatePullback
    (derivative : CoverCoordinates →L[Real] CoverCoordinates)
    (tensor : CovariantTwoTensorModel) : CovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem ptDerivativeCoordinates_apply
    (point current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).baseSet)
    (hPTCurrent : reflectedSpherePT period hPeriod current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (reflectedSpherePT period hPeriod point)).baseSet)
    (vector : CoverCoordinates) :
    ptDerivativeCoordinates period hPeriod point current vector =
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (reflectedSpherePT period hPeriod point)).linearMapAt Real
          (reflectedSpherePT period hPeriod current)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (reflectedSpherePT period hPeriod) current
            ((trivializationAt CoverCoordinates (TangentFiber period hPeriod)
              point).symm current vector)) := by
  rw [show ptDerivativeCoordinates period hPeriod point current =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
        CoverCoordinates (TangentFiber period hPeriod)
        point current (reflectedSpherePT period hPeriod point)
        (reflectedSpherePT period hPeriod current)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) current) by
      rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hPTCurrent]
  rw [Trivialization.linearMapAt_apply, if_pos hPTCurrent]
  rfl

private theorem ptPullbackTensorCoordinates_eq
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).baseSet)
    (hPTCurrent : reflectedSpherePT period hPeriod current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (reflectedSpherePT period hPeriod point)).baseSet) :
    ptPullbackTensorCoordinates period hPeriod tensor point current =
      coordinatePullback
        (ptDerivativeCoordinates period hPeriod point current)
        (ptTensorCoordinates period hPeriod tensor point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show ptPullbackTensorCoordinates period hPeriod tensor point current first second =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
        (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
        point current point current
        (ptTensorPullback period hPeriod tensor.tensor.toTensorField current)
        first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [ptTensorPullback_apply]
  simp only [coordinatePullback, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show ptTensorCoordinates period hPeriod tensor point current
        (ptDerivativeCoordinates period hPeriod point current first)
        (ptDerivativeCoordinates period hPeriod point current second) =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
        (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
        (reflectedSpherePT period hPeriod point)
        (reflectedSpherePT period hPeriod current)
        (reflectedSpherePT period hPeriod point)
        (reflectedSpherePT period hPeriod current)
        (tensor.tensor (reflectedSpherePT period hPeriod current))
        (ptDerivativeCoordinates period hPeriod point current first)
        (ptDerivativeCoordinates period hPeriod point current second) by rfl]
  rw [inCoordinates_apply_eq₂ hPTCurrent hPTCurrent (Set.mem_univ _)]
  rw [ptDerivativeCoordinates_apply period hPeriod point current hCurrent hPTCurrent first,
    ptDerivativeCoordinates_apply period hPeriod point current hCurrent hPTCurrent second]
  simp only [Trivialization.symm_linearMapAt _ hPTCurrent]
  rfl

/-- Analyticity of PT and smoothness of the input tensor discharge the local
dependent-Hom regularity contract. -/
theorem analyticPTTensorPullbackLocalSmoothness :
    AnalyticPTTensorPullbackLocalSmoothness period hPeriod := by
  intro tensor point
  have hD :=
    (reflectedSpherePT_contMDiff period hPeriod).contMDiffAt.mfderiv_const
      (x₀ := point) (m := ∞) (by simp)
  have hPT := (reflectedSpherePT_contMDiff period hPeriod).of_le
    (m := ∞) (by simp)
  have hTensor := tensor.tensor.contMDiff.comp hPT
  have hTensorAt := hTensor point
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hD.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hD
  have hFormula := hPre.clm_comp hOuter
  rw [PTTensorPullbackSmoothAt, contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply hFormula.congr_of_eventuallyEq
  have hCurrent : ∀ᶠ current in 𝓝 point,
      current ∈
        (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).baseSet :=
    (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt CoverCoordinates (TangentFiber period hPeriod) point)
  have hPTCurrent : ∀ᶠ current in 𝓝 point,
      reflectedSpherePT period hPeriod current ∈
        (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
          (reflectedSpherePT period hPeriod point)).baseSet :=
    (reflectedSpherePT_contMDiff period hPeriod).continuous.continuousAt
      ((trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (reflectedSpherePT period hPeriod point)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates (TangentFiber period hPeriod)
            (reflectedSpherePT period hPeriod point)))
  filter_upwards [hCurrent, hPTCurrent] with current hCurrent' hPTCurrent'
  simpa only [ptPullbackTensorCoordinates, coordinatePullback,
    ptDerivativeCoordinates, ptTensorCoordinates, Function.comp_apply] using
      (ptPullbackTensorCoordinates_eq period hPeriod tensor point current
        hCurrent' hPTCurrent')

/-- Canonical smooth PT pullback, with no external regularity hypothesis. -/
def smoothPTTensorPullback
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D.smoothPTTensorPullback
    period hPeriod (analyticPTTensorPullbackLocalSmoothness period hPeriod) tensor

@[simp]
theorem smoothPTTensorPullback_apply
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (smoothPTTensorPullback period hPeriod tensor).tensor point first second =
      tensor.tensor (reflectedSpherePT period hPeriod point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point second) :=
  P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D.smoothPTTensorPullback_apply
    period hPeriod (analyticPTTensorPullbackLocalSmoothness period hPeriod) tensor
      point first second

@[simp]
theorem smoothPTTensorPullback_involutive
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothPTTensorPullback period hPeriod
      (smoothPTTensorPullback period hPeriod tensor) = tensor :=
  P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D.smoothPTTensorPullback_involutive
    period hPeriod (analyticPTTensorPullbackLocalSmoothness period hPeriod) tensor

end

end P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
end JanusFormal
