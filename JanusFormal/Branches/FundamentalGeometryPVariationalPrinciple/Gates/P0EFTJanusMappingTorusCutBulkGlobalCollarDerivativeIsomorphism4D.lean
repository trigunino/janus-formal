import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenCollarAmbientDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D

/-!
# Derivative isomorphism on the global cut-bulk collar
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalCollarDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkOpenCollarAmbientDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance openCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
  cutThroatOpenCollarChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

/-- Every point represented by the global collar chart has invertible natural derivative. -/
theorem cutBulkToAmbient_derivative_isomorphism_at_openCollarAttachment
    (collar : CutThroatOpenCollar period hPeriod) :
    CutBulkDerivativeIsomorphismAt period hPeriod
      (cutOpenCollarAttachment period hPeriod collar) := by
  change CutBulkDerivativeIsomorphismAt period hPeriod
    ((cutOpenCollarAttachmentPartialDiffeomorph period hPeriod) collar)
  let inclusion := cutOpenCollarAttachmentPartialDiffeomorph period hPeriod
  have hSource : collar ∈ inclusion.source := by
    change collar ∈ Set.univ
    exact Set.mem_univ collar
  let inclusionLocal := PartialDiffeomorph.isLocalDiffeomorphAt
    cutCollarModelWithCorners cutCollarModelWithCorners ∞ inclusion hSource
  let inclusionDerivative :=
    inclusionLocal.mfderivToContinuousLinearEquiv (by simp)
  obtain ⟨ambientDerivative, hAmbientDerivative⟩ :=
    cutBulkOpenCollarToAmbient_derivative_isomorphism period hPeriod collar
  refine ⟨inclusionDerivative.symm.trans ambientDerivative, ?_⟩
  have hInclusionSmooth : MDifferentiableAt cutCollarModelWithCorners
      cutCollarModelWithCorners inclusion collar :=
    (inclusion.contMDiffOn.contMDiffAt
      (inclusion.open_source.mem_nhds hSource)).mdifferentiableAt (by simp)
  have hBulkSmooth : MDifferentiableAt cutCollarModelWithCorners
      coverModelWithCorners (cutBulkToAmbient period hPeriod)
      (inclusion collar) :=
    (cutBulkToAmbient_contMDiff period hPeriod).mdifferentiableAt
      (x := inclusion collar) (by simp)
  have hOuter := mfderiv_comp collar hBulkSmooth hInclusionSmooth
  have hFunction : cutBulkToAmbient period hPeriod ∘ inclusion =
      cutBulkOpenCollarToAmbient period hPeriod := by
    funext current
    rfl
  rw [hFunction] at hOuter
  apply ContinuousLinearMap.ext
  intro vector
  change ambientDerivative (inclusionDerivative.symm vector) = _
  have hApply := DFunLike.congr_fun hOuter (inclusionDerivative.symm vector)
  change mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkOpenCollarToAmbient period hPeriod) collar
        (inclusionDerivative.symm vector) =
    mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod) (inclusion collar)
      (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
        inclusion collar (inclusionDerivative.symm vector)) at hApply
  rw [← DFunLike.congr_fun hAmbientDerivative] at hApply
  have hInclusionDerivativeApply :
      mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
        inclusion collar (inclusionDerivative.symm vector) = vector := by
    rw [← DFunLike.congr_fun
      (inclusionLocal.mfderivToContinuousLinearEquiv_coe (by simp))]
    exact inclusionDerivative.apply_symm_apply vector
  rw [hInclusionDerivativeApply] at hApply
  simpa using hApply

/-- Global open-collar points inherit the differential certificate. -/
theorem cutBulkToAmbient_derivative_isomorphism_on_openCollar
    (bulk : PositiveHemisphereCutBulk period hPeriod)
    (hBulk : bulk ∈ Set.range (cutOpenCollarAttachment period hPeriod)) :
    CutBulkDerivativeIsomorphismAt period hPeriod bulk := by
  rcases hBulk with ⟨collar, rfl⟩
  exact cutBulkToAmbient_derivative_isomorphism_at_openCollarAttachment
    period hPeriod collar

end
end P0EFTJanusMappingTorusCutBulkGlobalCollarDerivativeIsomorphism4D
end JanusFormal
