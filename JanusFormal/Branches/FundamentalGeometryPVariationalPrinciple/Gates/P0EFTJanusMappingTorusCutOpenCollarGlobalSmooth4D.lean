import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D

/-! # Smoothness of the open-collar attachment in the global atlas -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutOpenCollarGlobalSmooth4D

set_option autoImplicit false
noncomputable section
local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The collar attachment is smooth for the global cut-bulk atlas. -/
theorem cutOpenCollarAttachment_contMDiff :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatFiniteCollarChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := cutBulkGlobalChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (cutOpenCollarAttachment period hPeriod) := by
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
  have hLocal : ChartedSpace.LiftPropOn
      (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
      attachment attachment.source := by
    intro collarPoint hSource
    refine ⟨(continuous_cutOpenCollarAttachment period hPeriod).continuousWithinAt,
      ?_⟩
    let collarChart := chartAt CutCollarModel collarPoint
    let bulkChart := chartAt CutCollarModel (attachment collarPoint)
    let transition := (collarChart.symm.trans attachment).trans bulkChart
    have hTransition : transition ∈
        contDiffGroupoid ∞ cutCollarModelWithCorners := by
      by_cases hCap : attachment collarPoint ∈
          cutBulkOpenCap period hPeriod
      · have hGlobalChart : bulkChart =
            liftedCutBulkCapChart period hPeriod
              ⟨attachment collarPoint, hCap⟩ := by
          change cutBulkGlobalChartAt period hPeriod (attachment collarPoint) = _
          simp [cutBulkGlobalChartAt, hCap]
        simpa only [transition, collarChart, bulkChart, hGlobalChart,
          attachment, liftedCutBulkCollarChart,
          OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm] using
          liftedCutBulkCollarCapTransition_mem_contDiffGroupoid period hPeriod
            collarPoint ⟨attachment collarPoint, hCap⟩
      · have hGlobalChart : bulkChart =
            liftedCutBulkCollarChart period hPeriod
              (attachment.symm (attachment collarPoint)) := by
          change cutBulkGlobalChartAt period hPeriod (attachment collarPoint) = _
          simp [cutBulkGlobalChartAt, hCap, attachment]
        simpa only [transition, collarChart, bulkChart, hGlobalChart,
          attachment, liftedCutBulkCollarChart,
          OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm] using
          liftedCutBulkCollarCollarTransition_mem_contDiffGroupoid
            period hPeriod collarPoint
              (attachment.symm (attachment collarPoint))
    have hPoint : collarChart collarPoint ∈ transition.source := by
      simp [transition, collarChart, bulkChart, hSource]
    have hSourceSubset : transition.source ⊆
        collarChart.symm ⁻¹' attachment.source := by
      intro coordinate hCoordinate
      simp only [transition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff,
        mem_preimage] at hCoordinate ⊢
      exact hCoordinate.1.2
    change (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
      transition (collarChart.symm ⁻¹' attachment.source)
        (collarChart collarPoint)
    rw [transition.isLocalStructomorphWithinAt_iff'
      hSourceSubset (Or.inl hPoint)]
    intro _
    exact ⟨transition, hTransition, Subset.rfl,
      Set.eqOn_refl transition transition.source, hPoint⟩
  have hSmoothOn :=
    (isLocalStructomorphOn_contDiffGroupoid_iff attachment).mp hLocal |>.1
  rw [← contMDiffOn_univ]
  simpa [attachment, cutOpenCollarAttachmentPartialHomeomorph] using hSmoothOn

end
end P0EFTJanusMappingTorusCutOpenCollarGlobalSmooth4D
end JanusFormal
