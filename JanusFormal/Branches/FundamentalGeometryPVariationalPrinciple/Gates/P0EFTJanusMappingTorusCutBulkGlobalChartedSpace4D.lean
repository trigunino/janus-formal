import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D

/-!
# Global charted space on the cut bulk

The collar and intrinsic-cap charts are lifted through their open embeddings
and selected on their two-open cover. Smooth compatibility is a separate gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D

set_option autoImplicit false
noncomputable section
local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open Set Topology
open scoped Manifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D

variable (period : Real) (hPeriod : period ≠ 0)

private def cutThroatBoundaryBasePoint :
    CutThroatBoundary period hPeriod :=
  let standard : StandardEquatorialTwoSphere :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  mappingTorusMk (orientationDoubleData period hPeriod)
    ⟨equatorialTwoSphereHomeomorph.symm standard, 0⟩

private instance cutThroatOpenCollarNonempty :
    Nonempty (CutThroatOpenCollar period hPeriod) := by
  let boundary := cutThroatBoundaryBasePoint period hPeriod
  exact ⟨⟨(boundary, ⟨0, by norm_num, by norm_num⟩), by norm_num⟩⟩

private instance cutBulkOpenCapNonempty :
    Nonempty (CutBulkOpenCap period hPeriod) := by
  let boundary := cutThroatBoundaryBasePoint period hPeriod
  let normal : CutCollarInterval := ⟨(1 : Real) / 2, by norm_num, by norm_num⟩
  let collar : CutThroatOpenCollar period hPeriod :=
    ⟨(boundary, normal), by norm_num [normal]⟩
  refine ⟨⟨cutOpenCollarAttachment period hPeriod collar, ?_⟩⟩
  change 0 < cutBulkLatitudeCoordinate period hPeriod
    (cutOpenCollarAttachment period hPeriod collar)
  change 0 < cutBulkLatitudeCoordinate period hPeriod
    (cutCollarAttachment period hPeriod collar.1)
  rw [cutBulkLatitudeCoordinate_cutCollarAttachment]
  change 0 < Real.sin ((1 : Real) / 2)
  exact Real.sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [Real.pi_gt_three])

/-- Open partial homeomorphism attaching the collar to the cut bulk. -/
def cutOpenCollarAttachmentPartialHomeomorph :
    OpenPartialHomeomorph (CutThroatOpenCollar period hPeriod)
      (PositiveHemisphereCutBulk period hPeriod) :=
  (cutOpenCollarAttachment_isOpenEmbedding period hPeriod)
    |>.toOpenPartialHomeomorph (cutOpenCollarAttachment period hPeriod)

/-- Open partial homeomorphism including the intrinsic cap. -/
def cutBulkOpenCapInclusionPartialHomeomorph :
    OpenPartialHomeomorph (CutBulkOpenCap period hPeriod)
      (PositiveHemisphereCutBulk period hPeriod) :=
  (cutBulkOpenCap_subtypeVal_isOpenEmbedding period hPeriod)
    |>.toOpenPartialHomeomorph Subtype.val

/-- A collar chart lifted to the whole cut bulk. -/
def liftedCutBulkCollarChart
    (point : CutThroatOpenCollar period hPeriod) :
    OpenPartialHomeomorph (PositiveHemisphereCutBulk period hPeriod)
      CutCollarModel :=
  (cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm.trans
    (letI := cutThroatOpenCollarChartedSpace period hPeriod
     chartAt CutCollarModel point)

/-- A common-model cap chart lifted to the whole cut bulk. -/
def liftedCutBulkCapChart
    (point : CutBulkOpenCap period hPeriod) :
    OpenPartialHomeomorph (PositiveHemisphereCutBulk period hPeriod)
      CutCollarModel :=
  (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).symm.trans
    (letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
     chartAt CutCollarModel point)

/-- Preferred global chart: cap in the positive interior, collar on the cut
boundary. -/
def cutBulkGlobalChartAt
    (bulk : PositiveHemisphereCutBulk period hPeriod) :
    OpenPartialHomeomorph (PositiveHemisphereCutBulk period hPeriod)
      CutCollarModel :=
  if hCap : bulk ∈ cutBulkOpenCap period hPeriod then
    liftedCutBulkCapChart period hPeriod ⟨bulk, hCap⟩
  else
    liftedCutBulkCollarChart period hPeriod
      ((cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm bulk)

theorem mem_source_cutBulkGlobalChartAt
    (bulk : PositiveHemisphereCutBulk period hPeriod) :
    bulk ∈ (cutBulkGlobalChartAt period hPeriod bulk).source := by
  by_cases hCap : bulk ∈ cutBulkOpenCap period hPeriod
  · letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    let capPoint : CutBulkOpenCap period hPeriod := ⟨bulk, hCap⟩
    rw [cutBulkGlobalChartAt, dif_pos hCap]
    rw [liftedCutBulkCapChart, OpenPartialHomeomorph.trans_source]
    constructor
    · change bulk ∈
        (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).target
      rw [cutBulkOpenCapInclusionPartialHomeomorph,
        IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨capPoint, rfl⟩
    · have hInverse :
          (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).symm bulk =
            capPoint := by
        rw [← show
          (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod) capPoint =
            bulk by rfl]
        exact (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).left_inv
          (by rw [cutBulkOpenCapInclusionPartialHomeomorph,
              IsOpenEmbedding.toOpenPartialHomeomorph_source]
              trivial)
      change (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).symm bulk ∈
        (chartAt CutCollarModel capPoint).source
      rw [hInverse]
      exact mem_chart_source CutCollarModel _
  · have hCollar : bulk ∈
        Set.range (cutOpenCollarAttachment period hPeriod) := by
      have hCover := openCollar_union_openCap period hPeriod
      have : bulk ∈ Set.range (cutOpenCollarAttachment period hPeriod) ∪
          cutBulkOpenCap period hPeriod := by rw [hCover]; trivial
      exact this.resolve_right hCap
    simp [cutBulkGlobalChartAt, hCap, liftedCutBulkCollarChart,
      cutOpenCollarAttachmentPartialHomeomorph, hCollar]

/-- Global topological atlas generated by the preferred lifted charts. -/
@[implicit_reducible] def cutBulkGlobalChartedSpace :
    ChartedSpace CutCollarModel
      (PositiveHemisphereCutBulk period hPeriod) where
  atlas := Set.range (cutBulkGlobalChartAt period hPeriod)
  chartAt := cutBulkGlobalChartAt period hPeriod
  mem_chart_source := mem_source_cutBulkGlobalChartAt period hPeriod
  chart_mem_atlas point := ⟨point, rfl⟩

end
end P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
end JanusFormal
