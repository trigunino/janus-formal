import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapAttachmentTransition4D

/-! # Coordinate compatibility across the intrinsic collar--cap overlap -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkCollarCapPartialDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarCapAttachmentTransition4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem liftedTransition_mem_groupoid
    {H A M : Type*} [TopologicalSpace H] [TopologicalSpace A]
    [TopologicalSpace M] [ChartedSpace H A]
    (G : StructureGroupoid H) [HasGroupoid A G] [ClosedUnderRestriction G]
    (embedding : OpenPartialHomeomorph A M)
    (hSource : embedding.source = Set.univ)
    (first second : OpenPartialHomeomorph A H)
    (hFirst : first ∈ atlas H A) (hSecond : second ∈ atlas H A) :
    (embedding.symm.trans first).symm.trans
        (embedding.symm.trans second) ∈ G := by
  have hLocal := G.compatible hFirst hSecond
  have hCancel := embedding.self_trans_symm
  have hEquivalent :
      (first.symm.trans (embedding.trans embedding.symm)).trans second ≈
        (first.symm.trans
          (OpenPartialHomeomorph.ofSet embedding.source embedding.open_source)).trans
            second :=
    (OpenPartialHomeomorph.EqOnSource.trans'
      first.symm.eqOnSource_refl hCancel).trans' second.eqOnSource_refl
  apply G.mem_of_eqOnSource hLocal
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
    OpenPartialHomeomorph.ofSet_trans, hSource,
    OpenPartialHomeomorph.restr_univ] using hEquivalent

/-- Every local collar chart and local common-model cap chart are compatible
through the certified smooth partial diffeomorphism. -/
theorem intrinsicCollarCapCoordinateTransition_mem_contDiffGroupoid
    (first : OpenPartialHomeomorph (CutThroatOpenCollar period hPeriod)
      CutCollarModel)
    (second : OpenPartialHomeomorph (CutBulkOpenCap period hPeriod)
      CutCollarModel) :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    first ∈ atlas CutCollarModel (CutThroatOpenCollar period hPeriod) →
    second ∈ atlas CutCollarModel (CutBulkOpenCap period hPeriod) →
    (first.symm.trans
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).toOpenPartialHomeomorph).trans
        second ∈ contDiffGroupoid ∞ cutCollarModelWithCorners := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  intro hFirst hSecond
  let deck :=
    (intrinsicCollarCapPartialDiffeomorph period hPeriod).toOpenPartialHomeomorph
  let transition := (first.symm.trans deck).trans second
  have hLocal := intrinsicCollarCapPartialDiffeomorph_isLocalStructomorph
    period hPeriod
  apply (contDiffGroupoid ∞ cutCollarModelWithCorners).locality
  intro coordinate hCoordinate
  have hCoordinate' : coordinate ∈ first.target ∩
      first.symm ⁻¹' (deck.source ∩ deck ⁻¹' second.source) := by
    have h := hCoordinate
    simp only [deck, mfld_simps] at h ⊢
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hProperty :=
    StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid ∞ cutCollarModelWithCorners))
      ((contDiffGroupoid ∞ cutCollarModelWithCorners).subset_maximalAtlas hFirst)
      ((contDiffGroupoid ∞ cutCollarModelWithCorners).subset_maximalAtlas hSecond)
      hLocal hCoordinate'
  obtain ⟨localMap, hLocalMap, hEqual, hCoordinateLocal⟩ :=
    hProperty hCoordinate'.2.1
  let neighborhood := transition.source ∩ localMap.source
  refine ⟨neighborhood, transition.open_source.inter localMap.open_source,
    ⟨hCoordinate, hCoordinateLocal⟩, ?_⟩
  have hEqualTransition : Set.EqOn transition localMap neighborhood := by
    intro point hPoint
    have hSource : point ∈ first.target ∩
        first.symm ⁻¹' (deck.source ∩ deck ⁻¹' second.source) := by
      have h := hPoint.1
      simp only [deck, mfld_simps] at h ⊢
      exact ⟨h.1.1, h.1.2, h.2⟩
    apply hEqual
    constructor
    · change first.symm point ∈
        (intrinsicCollarCapPartialDiffeomorph period hPeriod).source
      exact hSource.2.1
    · exact hPoint.2
  rw [OpenPartialHomeomorph.restr_source_inter]
  exact (contDiffGroupoid ∞ cutCollarModelWithCorners).mem_of_eqOnSource
    (closedUnderRestriction' hLocalMap transition.open_source)
    (OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEqualTransition)

theorem intrinsicCollarCapAttachmentCoordinateTransition_mem_contDiffGroupoid
    (first : OpenPartialHomeomorph (CutThroatOpenCollar period hPeriod)
      CutCollarModel)
    (second : OpenPartialHomeomorph (CutBulkOpenCap period hPeriod)
      CutCollarModel) :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    first ∈ atlas CutCollarModel (CutThroatOpenCollar period hPeriod) →
    second ∈ atlas CutCollarModel (CutBulkOpenCap period hPeriod) →
    (first.symm.trans (intrinsicCollarCapAttachmentTransition period hPeriod)).trans
      second ∈ contDiffGroupoid ∞ cutCollarModelWithCorners := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  intro hFirst hSecond
  have hSmooth := intrinsicCollarCapCoordinateTransition_mem_contDiffGroupoid
    period hPeriod first second hFirst hSecond
  have hDeck :=
    intrinsicCollarCapPartialDiffeomorph_eqOnSource_attachmentTransition
      period hPeriod
  have hTransition :
      (first.symm.trans
        (intrinsicCollarCapPartialDiffeomorph period hPeriod).toOpenPartialHomeomorph).trans
          second ≈
        (first.symm.trans
          (intrinsicCollarCapAttachmentTransition period hPeriod)).trans second :=
    (OpenPartialHomeomorph.EqOnSource.trans'
      first.symm.eqOnSource_refl hDeck).trans' second.eqOnSource_refl
  exact (contDiffGroupoid ∞ cutCollarModelWithCorners).mem_of_eqOnSource
    hSmooth (Setoid.symm hTransition)

theorem liftedCutBulkCollarCapTransition_mem_contDiffGroupoid
    (collarPoint : CutThroatOpenCollar period hPeriod)
    (capPoint : CutBulkOpenCap period hPeriod) :
    (liftedCutBulkCollarChart period hPeriod collarPoint).symm.trans
        (liftedCutBulkCapChart period hPeriod capPoint) ∈
      contDiffGroupoid ∞ cutCollarModelWithCorners := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  have hTransition :=
    intrinsicCollarCapAttachmentCoordinateTransition_mem_contDiffGroupoid
      period hPeriod (chartAt CutCollarModel collarPoint)
        (chartAt CutCollarModel capPoint)
      (chart_mem_atlas CutCollarModel collarPoint)
      (chart_mem_atlas CutCollarModel capPoint)
  simpa only [liftedCutBulkCollarChart, liftedCutBulkCapChart,
    intrinsicCollarCapAttachmentTransition,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_assoc] using hTransition

theorem liftedCutBulkCapCollarTransition_mem_contDiffGroupoid
    (capPoint : CutBulkOpenCap period hPeriod)
    (collarPoint : CutThroatOpenCollar period hPeriod) :
    (liftedCutBulkCapChart period hPeriod capPoint).symm.trans
        (liftedCutBulkCollarChart period hPeriod collarPoint) ∈
      contDiffGroupoid ∞ cutCollarModelWithCorners := by
  have hTransition :=
    (contDiffGroupoid ∞ cutCollarModelWithCorners).symm
      (liftedCutBulkCollarCapTransition_mem_contDiffGroupoid
        period hPeriod collarPoint capPoint)
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] using hTransition

theorem liftedCutBulkCollarCollarTransition_mem_contDiffGroupoid
    (first second : CutThroatOpenCollar period hPeriod) :
    (liftedCutBulkCollarChart period hPeriod first).symm.trans
        (liftedCutBulkCollarChart period hPeriod second) ∈
      contDiffGroupoid ∞ cutCollarModelWithCorners := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  apply liftedTransition_mem_groupoid
    (contDiffGroupoid ∞ cutCollarModelWithCorners)
    (cutOpenCollarAttachmentPartialHomeomorph period hPeriod)
  · simp [cutOpenCollarAttachmentPartialHomeomorph]
  · exact chart_mem_atlas CutCollarModel first
  · exact chart_mem_atlas CutCollarModel second

theorem liftedCutBulkCapCapTransition_mem_contDiffGroupoid
    (first second : CutBulkOpenCap period hPeriod) :
    (liftedCutBulkCapChart period hPeriod first).symm.trans
        (liftedCutBulkCapChart period hPeriod second) ∈
      contDiffGroupoid ∞ cutCollarModelWithCorners := by
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  apply liftedTransition_mem_groupoid
    (contDiffGroupoid ∞ cutCollarModelWithCorners)
    (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod)
  · simp [cutBulkOpenCapInclusionPartialHomeomorph]
  · exact chart_mem_atlas CutCollarModel first
  · exact chart_mem_atlas CutCollarModel second

end
end P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D
end JanusFormal
