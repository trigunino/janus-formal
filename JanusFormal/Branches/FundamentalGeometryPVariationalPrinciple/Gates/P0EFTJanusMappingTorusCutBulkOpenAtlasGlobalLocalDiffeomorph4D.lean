import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutOpenCollarGlobalSmooth4D

/-!
# Local diffeomorphisms of the global cut-bulk open atlas

Both open pieces used to define the global atlas are smooth in both directions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D

set_option autoImplicit false
noncomputable section
local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem cutOpenCollarAttachment_localStructomorph :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatFiniteCollarChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := cutBulkGlobalChartedSpace period hPeriod
    ChartedSpace.LiftPropOn
      (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
      (cutOpenCollarAttachmentPartialHomeomorph period hPeriod)
      (cutOpenCollarAttachmentPartialHomeomorph period hPeriod).source := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ∞
      (CutThroatBoundary period hPeriod) :=
    (cutThroatBoundary_isManifold period hPeriod).of_le le_top
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatFiniteCollar period hPeriod) :=
    (cutThroatFiniteCollar_isManifold period hPeriod).of_le le_top
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  letI := cutBulkGlobalChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobal_isManifold period hPeriod
  let attachment := cutOpenCollarAttachmentPartialHomeomorph period hPeriod
  intro collarPoint hSource
  refine ⟨attachment.continuousAt hSource |>.continuousWithinAt, ?_⟩
  let collarChart := chartAt CutCollarModel collarPoint
  let bulkChart := chartAt CutCollarModel (attachment collarPoint)
  let transition := (collarChart.symm.trans attachment).trans bulkChart
  have hTransition : transition ∈
      contDiffGroupoid ∞ cutCollarModelWithCorners := by
    by_cases hCap : attachment collarPoint ∈ cutBulkOpenCap period hPeriod
    · have hGlobalChart : bulkChart =
          liftedCutBulkCapChart period hPeriod ⟨attachment collarPoint, hCap⟩ := by
        change cutBulkGlobalChartAt period hPeriod (attachment collarPoint) = _
        simp [cutBulkGlobalChartAt, hCap]
      simpa only [transition, collarChart, bulkChart, hGlobalChart, attachment,
        liftedCutBulkCollarChart,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using
        liftedCutBulkCollarCapTransition_mem_contDiffGroupoid period hPeriod
          collarPoint ⟨attachment collarPoint, hCap⟩
    · have hGlobalChart : bulkChart =
          liftedCutBulkCollarChart period hPeriod
            (attachment.symm (attachment collarPoint)) := by
        change cutBulkGlobalChartAt period hPeriod (attachment collarPoint) = _
        simp [cutBulkGlobalChartAt, hCap, attachment]
      simpa only [transition, collarChart, bulkChart, hGlobalChart, attachment,
        liftedCutBulkCollarChart,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using
        liftedCutBulkCollarCollarTransition_mem_contDiffGroupoid period hPeriod
          collarPoint (attachment.symm (attachment collarPoint))
  have hSource' : collarPoint ∈ attachment.source := by
    simpa [attachment] using hSource
  have hPoint : collarChart collarPoint ∈ transition.source := by
    simp [transition, collarChart, bulkChart, hSource']
  have hSourceSubset : transition.source ⊆
      collarChart.symm ⁻¹' attachment.source := by
    intro coordinate hCoordinate
    simp only [transition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
      at hCoordinate ⊢
    exact hCoordinate.1.2
  change (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
    transition (collarChart.symm ⁻¹' attachment.source) (collarChart collarPoint)
  rw [transition.isLocalStructomorphWithinAt_iff'
    hSourceSubset (Or.inl hPoint)]
  intro _
  exact ⟨transition, hTransition, Subset.rfl,
    Set.eqOn_refl transition transition.source, hPoint⟩

private theorem cutBulkOpenCapInclusion_localStructomorph :
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    letI := cutBulkGlobalChartedSpace period hPeriod
    ChartedSpace.LiftPropOn
      (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
      (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod)
      (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).source := by
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  letI := cutBulkGlobalChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobal_isManifold period hPeriod
  let attachment := cutBulkOpenCapInclusionPartialHomeomorph period hPeriod
  intro capPoint hSource
  refine ⟨attachment.continuousAt hSource |>.continuousWithinAt, ?_⟩
  let capChart := chartAt CutCollarModel capPoint
  let bulkChart := chartAt CutCollarModel (attachment capPoint)
  let transition := (capChart.symm.trans attachment).trans bulkChart
  have hCap : attachment capPoint ∈ cutBulkOpenCap period hPeriod := capPoint.2
  have hGlobalChart : bulkChart =
      liftedCutBulkCapChart period hPeriod ⟨attachment capPoint, hCap⟩ := by
    change cutBulkGlobalChartAt period hPeriod (attachment capPoint) = _
    simp [cutBulkGlobalChartAt, hCap]
  have hTransition : transition ∈
      contDiffGroupoid ∞ cutCollarModelWithCorners := by
    simpa only [transition, capChart, bulkChart, hGlobalChart, attachment,
      liftedCutBulkCapChart,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using
      liftedCutBulkCapCapTransition_mem_contDiffGroupoid period hPeriod
        capPoint ⟨attachment capPoint, hCap⟩
  have hSource' : capPoint ∈ attachment.source := by
    simpa [attachment] using hSource
  have hPoint : capChart capPoint ∈ transition.source := by
    simp [transition, capChart, bulkChart, hSource']
  have hSourceSubset : transition.source ⊆
      capChart.symm ⁻¹' attachment.source := by
    intro coordinate hCoordinate
    simp only [transition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
      at hCoordinate ⊢
    exact hCoordinate.1.2
  change (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
    transition (capChart.symm ⁻¹' attachment.source) (capChart capPoint)
  rw [transition.isLocalStructomorphWithinAt_iff'
    hSourceSubset (Or.inl hPoint)]
  intro _
  exact ⟨transition, hTransition, Subset.rfl,
    Set.eqOn_refl transition transition.source, hPoint⟩

/-- The collar chart is a genuine global-atlas partial diffeomorphism. -/
def cutOpenCollarAttachmentPartialDiffeomorph :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatFiniteCollarChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := cutBulkGlobalChartedSpace period hPeriod
    PartialDiffeomorph cutCollarModelWithCorners cutCollarModelWithCorners
      (CutThroatOpenCollar period hPeriod)
      (PositiveHemisphereCutBulk period hPeriod) ∞ := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ∞
      (CutThroatBoundary period hPeriod) :=
    (cutThroatBoundary_isManifold period hPeriod).of_le le_top
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatFiniteCollar period hPeriod) :=
    (cutThroatFiniteCollar_isManifold period hPeriod).of_le le_top
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  letI := cutBulkGlobalChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobal_isManifold period hPeriod
  have hSmooth := (isLocalStructomorphOn_contDiffGroupoid_iff
      (cutOpenCollarAttachmentPartialHomeomorph period hPeriod)).mp
    (cutOpenCollarAttachment_localStructomorph period hPeriod)
  let attachment := cutOpenCollarAttachmentPartialHomeomorph period hPeriod
  exact
    { __ := attachment
      contMDiffOn_toFun := hSmooth.1
      contMDiffOn_invFun := hSmooth.2 }

/-- The cap chart is a genuine global-atlas partial diffeomorphism. -/
def cutBulkOpenCapInclusionPartialDiffeomorph :
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    letI := cutBulkGlobalChartedSpace period hPeriod
    PartialDiffeomorph cutCollarModelWithCorners cutCollarModelWithCorners
      (CutBulkOpenCap period hPeriod)
      (PositiveHemisphereCutBulk period hPeriod) ∞ := by
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  letI := cutBulkGlobalChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobal_isManifold period hPeriod
  have hSmooth := (isLocalStructomorphOn_contDiffGroupoid_iff
      (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod)).mp
    (cutBulkOpenCapInclusion_localStructomorph period hPeriod)
  let attachment := cutBulkOpenCapInclusionPartialHomeomorph period hPeriod
  exact
    { __ := attachment
      contMDiffOn_toFun := hSmooth.1
      contMDiffOn_invFun := hSmooth.2 }

end
end P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
end JanusFormal
