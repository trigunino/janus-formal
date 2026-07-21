import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenCapAmbientDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D

/-!
# Derivative isomorphism on the global cut-bulk cap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalCapDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkOpenCapAmbientDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance smoothCapChartedSpace :
    ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
  cutBulkOpenCapQuotientChartedSpace period hPeriod

local instance intrinsicCapStandardChartedSpace :
    ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
  intrinsicCutBulkOpenCapChartedSpace period hPeriod

local instance intrinsicCapCommonChartedSpace :
    ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
  intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod

local instance cutBulkChartedSpace : ChartedSpace CutCollarModel
    (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

private def smoothCapToIntrinsicStandardDiffeomorph :
    SmoothCutBulkOpenCap period hPeriod ≃ₘ^∞⟮coverModelWithCorners,
      coverModelWithCorners⟯ CutBulkOpenCap period hPeriod where
  toEquiv := (smoothCutBulkOpenCapHomeomorph period hPeriod).toEquiv
  contMDiff_toFun := (smoothCapHomeomorph_contMDiff period hPeriod).of_le (by simp)
  contMDiff_invFun :=
    (smoothCapHomeomorph_symm_contMDiff period hPeriod).of_le (by simp)

private def intrinsicCapStandardToCommonDiffeomorph :
    CutBulkOpenCap period hPeriod ≃ₘ^∞⟮coverModelWithCorners,
      cutCollarModelWithCorners⟯ CutBulkOpenCap period hPeriod where
  toEquiv := Equiv.refl _
  contMDiff_toFun := intrinsicCapStandardToCommon_contMDiff period hPeriod
  contMDiff_invFun := intrinsicCapCommonToStandard_contMDiff period hPeriod

private def smoothCapToIntrinsicCommonDiffeomorph :
    SmoothCutBulkOpenCap period hPeriod ≃ₘ^∞⟮coverModelWithCorners,
      cutCollarModelWithCorners⟯ CutBulkOpenCap period hPeriod :=
  (smoothCapToIntrinsicStandardDiffeomorph period hPeriod).trans
    (intrinsicCapStandardToCommonDiffeomorph period hPeriod)

private theorem smoothCapToIntrinsicCommon_value
    (cap : SmoothCutBulkOpenCap period hPeriod) :
    (smoothCapToIntrinsicCommonDiffeomorph period hPeriod cap).1 =
      smoothCutBulkOpenCapToCutBulk period hPeriod cap := by
  rfl

private theorem cutBulkToAmbient_derivative_isomorphism_of_analyticCap
    (analyticCap : SmoothCutBulkOpenCap period hPeriod) :
    CutBulkDerivativeIsomorphismAt period hPeriod
      (smoothCapToIntrinsicCommonDiffeomorph period hPeriod analyticCap).1 := by
  let capDiffeomorphism := smoothCapToIntrinsicCommonDiffeomorph period hPeriod
  let cap := capDiffeomorphism analyticCap
  let inclusion := cutBulkOpenCapInclusionPartialDiffeomorph period hPeriod
  change CutBulkDerivativeIsomorphismAt period hPeriod (inclusion cap)
  have hInclusionSource : cap ∈ inclusion.source := by
    change cap ∈ Set.univ
    exact Set.mem_univ cap
  let inclusionLocal := PartialDiffeomorph.isLocalDiffeomorphAt
    cutCollarModelWithCorners cutCollarModelWithCorners ∞ inclusion
      hInclusionSource
  let capDerivative := capDiffeomorphism.mfderivToContinuousLinearEquiv
    (by simp) analyticCap
  let inclusionDerivative := inclusionLocal.mfderivToContinuousLinearEquiv
    (by simp)
  obtain ⟨ambientDerivative, hAmbientDerivative⟩ :=
    smoothCutBulkOpenCapToAmbient_derivative_isomorphism
      period hPeriod analyticCap
  refine ⟨inclusionDerivative.symm.trans
      (capDerivative.symm.trans ambientDerivative), ?_⟩

  have hCapSmooth : MDifferentiableAt coverModelWithCorners
      cutCollarModelWithCorners capDiffeomorphism analyticCap :=
    capDiffeomorphism.contMDiff.mdifferentiable (by simp) analyticCap
  have hInclusionSmooth : MDifferentiableAt cutCollarModelWithCorners
      cutCollarModelWithCorners inclusion cap :=
    (inclusion.contMDiffOn.contMDiffAt
      (inclusion.open_source.mem_nhds hInclusionSource)).mdifferentiableAt
        (by simp)
  have hInner := mfderiv_comp analyticCap hInclusionSmooth hCapSmooth
  have hBulkSmooth : MDifferentiableAt cutCollarModelWithCorners
      coverModelWithCorners (cutBulkToAmbient period hPeriod) (inclusion cap) :=
    (cutBulkToAmbient_contMDiff period hPeriod).mdifferentiable (by simp)
      (inclusion cap)
  have hCompositeSmooth : MDifferentiableAt coverModelWithCorners
      cutCollarModelWithCorners (inclusion ∘ capDiffeomorphism) analyticCap :=
    hInclusionSmooth.comp analyticCap hCapSmooth
  have hOuter := mfderiv_comp analyticCap hBulkSmooth hCompositeSmooth
  have hFunction : cutBulkToAmbient period hPeriod ∘
      (inclusion ∘ capDiffeomorphism) =
      smoothCutBulkOpenCapToAmbient period hPeriod := by
    funext current
    rw [Function.comp_apply, Function.comp_apply,
      smoothCutBulkOpenCapToAmbient_eq_bulk,
      ← smoothCapToIntrinsicCommon_value]
    rfl
  have hOuter' : mfderiv coverModelWithCorners coverModelWithCorners
      (smoothCutBulkOpenCapToAmbient period hPeriod) analyticCap =
    (mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod) (inclusion cap)).comp
      (mfderiv coverModelWithCorners cutCollarModelWithCorners
        (inclusion ∘ capDiffeomorphism) analyticCap) := by
    rw [← hFunction]
    exact hOuter
  rw [hInner] at hOuter'

  apply ContinuousLinearMap.ext
  intro vector
  change ambientDerivative
      (capDerivative.symm (inclusionDerivative.symm vector)) = _
  have hApply := DFunLike.congr_fun hOuter'
    (capDerivative.symm (inclusionDerivative.symm vector))
  change mfderiv coverModelWithCorners coverModelWithCorners
      (smoothCutBulkOpenCapToAmbient period hPeriod) analyticCap
        (capDerivative.symm (inclusionDerivative.symm vector)) =
    mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod) (inclusion cap)
      (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners inclusion cap
        (mfderiv coverModelWithCorners cutCollarModelWithCorners
          capDiffeomorphism analyticCap
          (capDerivative.symm (inclusionDerivative.symm vector)))) at hApply
  rw [← DFunLike.congr_fun hAmbientDerivative,
    ← DFunLike.congr_fun
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe capDiffeomorphism
        (by simp)),
    ← DFunLike.congr_fun
      (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
        inclusionLocal (by simp))] at hApply
  change ambientDerivative
      (capDerivative.symm (inclusionDerivative.symm vector)) =
    mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod) (inclusion cap)
        (inclusionDerivative
          (capDerivative
            (capDerivative.symm (inclusionDerivative.symm vector)))) at hApply
  simpa using hApply

/-- Every point of the global open cap has an invertible natural derivative. -/
theorem cutBulkToAmbient_derivative_isomorphism_on_openCap
    (cap : CutBulkOpenCap period hPeriod) :
    CutBulkDerivativeIsomorphismAt period hPeriod cap.1 := by
  let analyticCap :=
    (smoothCapToIntrinsicCommonDiffeomorph period hPeriod).symm cap
  have h := cutBulkToAmbient_derivative_isomorphism_of_analyticCap
    period hPeriod analyticCap
  have hValue :
      smoothCapToIntrinsicCommonDiffeomorph period hPeriod analyticCap = cap :=
    (smoothCapToIntrinsicCommonDiffeomorph period hPeriod).apply_symm_apply cap
  simpa [hValue] using h

end
end P0EFTJanusMappingTorusCutBulkGlobalCapDerivativeIsomorphism4D
end JanusFormal
