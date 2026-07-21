import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapIntrinsicCompatibility4D

/-!
# Partial diffeomorphism between the full collar and cap opens
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapPartialDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapOverlapDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarCapIntrinsicCompatibility4D

private def openSubtypePartialDiffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners Real E H) (U : Opens M) (base : U) :
    PartialDiffeomorph I I U M ∞ := by
  letI : Nonempty U := ⟨base⟩
  exact
    { __ := U.2.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        intro point hPoint
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U]
        apply contMDiffWithinAt_id.congr_of_mem _ hPoint
        intro target hTarget
        exact U.2.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_right_inv
          Subtype.val hTarget }

variable (period : Real) (hPeriod : period ≠ 0)

private def positiveCollarBasePoint :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    cutThroatPositiveOpenCollarOpen period hPeriod := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  let cap : SmoothCutCapOverlap period hPeriod := Classical.choice inferInstance
  exact smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod
    ((smoothCutCollarCapOverlapDiffeomorph period hPeriod).symm cap)

private def intrinsicCapOverlapBasePoint :
    intrinsicCapOverlapOpen period hPeriod :=
  smoothCutCapOverlapToIntrinsicCapOpen period hPeriod (Classical.choice inferInstance)

/-- The collar--cap transition extended as a partial diffeomorphism whose
source and target are the actual overlap opens. -/
def intrinsicCollarCapPartialDiffeomorph :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    PartialDiffeomorph cutCollarModelWithCorners cutCollarModelWithCorners
      (CutThroatOpenCollar period hPeriod) (CutBulkOpenCap period hPeriod) ∞ := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  exact (openSubtypePartialDiffeomorph cutCollarModelWithCorners
      (cutThroatPositiveOpenCollarOpen period hPeriod)
      (positiveCollarBasePoint period hPeriod)).symm |>.trans
    ((intrinsicCollarCapOverlapDiffeomorph period hPeriod).toPartialDiffeomorph.trans
      (openSubtypePartialDiffeomorph cutCollarModelWithCorners
        (intrinsicCapOverlapOpen period hPeriod)
        (intrinsicCapOverlapBasePoint period hPeriod)))

@[simp] theorem intrinsicCollarCapPartialDiffeomorph_source :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    (intrinsicCollarCapPartialDiffeomorph period hPeriod).source =
      cutThroatPositiveOpenCollarOpen period hPeriod := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  ext point
  simp [intrinsicCollarCapPartialDiffeomorph, openSubtypePartialDiffeomorph,
    Diffeomorph.toPartialDiffeomorph]

@[simp] theorem intrinsicCollarCapPartialDiffeomorph_target :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    (intrinsicCollarCapPartialDiffeomorph period hPeriod).target =
      intrinsicCapOverlapOpen period hPeriod := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  ext point
  simp [intrinsicCollarCapPartialDiffeomorph, openSubtypePartialDiffeomorph,
    Diffeomorph.toPartialDiffeomorph]

theorem intrinsicCollarCapPartialDiffeomorph_bulk_eq_attachment
    (point : CutThroatOpenCollar period hPeriod)
    (hPoint : point ∈
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).source) :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ((intrinsicCollarCapPartialDiffeomorph period hPeriod point).1 :
      PositiveHemisphereCutBulk period hPeriod) =
        cutOpenCollarAttachment period hPeriod point := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  let overlap : cutThroatPositiveOpenCollarOpen period hPeriod :=
    ⟨point, by simpa using hPoint⟩
  have hInverse :
      (openSubtypePartialDiffeomorph cutCollarModelWithCorners
        (cutThroatPositiveOpenCollarOpen period hPeriod)
        (positiveCollarBasePoint period hPeriod)).symm point = overlap := by
    rw [← show (openSubtypePartialDiffeomorph cutCollarModelWithCorners
      (cutThroatPositiveOpenCollarOpen period hPeriod)
      (positiveCollarBasePoint period hPeriod)) overlap = point by rfl]
    apply (openSubtypePartialDiffeomorph cutCollarModelWithCorners
      (cutThroatPositiveOpenCollarOpen period hPeriod)
      (positiveCollarBasePoint period hPeriod)).left_inv
    simp [openSubtypePartialDiffeomorph]
  have hValue : intrinsicCollarCapPartialDiffeomorph period hPeriod point =
      (intrinsicCollarCapOverlapDiffeomorph period hPeriod overlap :
        intrinsicCapOverlapOpen period hPeriod) := by
    change ((intrinsicCollarCapOverlapDiffeomorph period hPeriod
      ((openSubtypePartialDiffeomorph cutCollarModelWithCorners
        (cutThroatPositiveOpenCollarOpen period hPeriod)
        (positiveCollarBasePoint period hPeriod)).symm point)).1 :
          CutBulkOpenCap period hPeriod) =
      (intrinsicCollarCapOverlapDiffeomorph period hPeriod overlap).1
    rw [hInverse]
  rw [hValue]
  exact intrinsicCollarCapOverlapDiffeomorph_bulk_eq_attachment
    period hPeriod overlap

theorem intrinsicCollarCapPartialDiffeomorph_contMDiffOn :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ContMDiffOn cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (intrinsicCollarCapPartialDiffeomorph period hPeriod)
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).source := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  exact (intrinsicCollarCapPartialDiffeomorph period hPeriod).contMDiffOn

theorem intrinsicCollarCapPartialDiffeomorph_symm_contMDiffOn :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ContMDiffOn cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).symm
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).target := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  exact (intrinsicCollarCapPartialDiffeomorph period hPeriod).symm.contMDiffOn

theorem intrinsicCollarCapPartialDiffeomorph_isLocalStructomorph :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ChartedSpace.LiftPropOn
      (contDiffGroupoid ∞ cutCollarModelWithCorners).IsLocalStructomorphWithinAt
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).toOpenPartialHomeomorph
      (intrinsicCollarCapPartialDiffeomorph period hPeriod).source := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  let transition :=
    (intrinsicCollarCapPartialDiffeomorph period hPeriod).toOpenPartialHomeomorph
  apply (isLocalStructomorphOn_contDiffGroupoid_iff
    (I := cutCollarModelWithCorners) (n := ∞) transition).2
  exact ⟨intrinsicCollarCapPartialDiffeomorph_contMDiffOn period hPeriod,
    intrinsicCollarCapPartialDiffeomorph_symm_contMDiffOn period hPeriod⟩

end
end P0EFTJanusMappingTorusCutBulkCollarCapPartialDiffeomorph4D
end JanusFormal
