import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapPartialDiffeomorph4D

/-! # Exact intrinsic collar--cap attachment transition -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapAttachmentTransition4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarCapPartialDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The topological transition induced by the two open embeddings. -/
def intrinsicCollarCapAttachmentTransition :
    OpenPartialHomeomorph (CutThroatOpenCollar period hPeriod)
      (CutBulkOpenCap period hPeriod) :=
  (cutOpenCollarAttachmentPartialHomeomorph period hPeriod).trans
    (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).symm

theorem intrinsicCollarCapAttachmentTransition_source :
    (intrinsicCollarCapAttachmentTransition period hPeriod).source =
      cutThroatPositiveOpenCollarOpen period hPeriod := by
  ext point
  rw [intrinsicCollarCapAttachmentTransition,
    OpenPartialHomeomorph.trans_source]
  simp only [cutOpenCollarAttachmentPartialHomeomorph,
    cutBulkOpenCapInclusionPartialHomeomorph,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, mem_inter_iff,
    mem_univ, true_and, mem_preimage, mem_range, cutBulkOpenCap]
  have hZero : (0 : Real) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hPoint : point.1.2.1 ∈
      Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [point.1.2.2.1, point.1.2.2.2,
      Real.pi_gt_three]
  constructor
  · rintro ⟨cap, hCap⟩
    have hPositive : 0 < cutBulkLatitudeCoordinate period hPeriod
        (cutOpenCollarAttachment period hPeriod point) := by
      rw [← hCap]
      exact cap.2
    change 0 < cutBulkLatitudeCoordinate period hPeriod
      (cutCollarAttachment period hPeriod point.1) at hPositive
    rw [cutBulkLatitudeCoordinate_cutCollarAttachment] at hPositive
    change 0 < point.1.2.1
    exact (Real.strictMonoOn_sin.lt_iff_lt hZero hPoint).mp (by
      simpa using hPositive)
  · intro hPositive
    change 0 < point.1.2.1 at hPositive
    refine ⟨⟨cutOpenCollarAttachment period hPeriod point, ?_⟩, rfl⟩
    change 0 < cutBulkLatitudeCoordinate period hPeriod
      (cutCollarAttachment period hPeriod point.1)
    rw [cutBulkLatitudeCoordinate_cutCollarAttachment]
    exact Real.sin_pos_of_pos_of_lt_pi hPositive
      (by linarith [point.1.2.2.2, Real.pi_gt_three])

/-- The smooth partial diffeomorphism is exactly the transition induced by
the two embeddings, up to the standard equivalence on their common source. -/
theorem intrinsicCollarCapPartialDiffeomorph_eqOnSource_attachmentTransition :
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    (intrinsicCollarCapPartialDiffeomorph period hPeriod).toOpenPartialHomeomorph ≈
      intrinsicCollarCapAttachmentTransition period hPeriod := by
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  constructor
  · change (intrinsicCollarCapPartialDiffeomorph period hPeriod).source = _
    rw [intrinsicCollarCapPartialDiffeomorph_source,
      intrinsicCollarCapAttachmentTransition_source]
  · intro point hPoint
    apply Subtype.ext
    change ((intrinsicCollarCapPartialDiffeomorph period hPeriod point).1 :
        PositiveHemisphereCutBulk period hPeriod) =
      ((intrinsicCollarCapAttachmentTransition period hPeriod point).1 :
        PositiveHemisphereCutBulk period hPeriod)
    rw [intrinsicCollarCapPartialDiffeomorph_bulk_eq_attachment
      period hPeriod point hPoint]
    have hTransitionSource : point ∈
        (intrinsicCollarCapAttachmentTransition period hPeriod).source := by
      rw [intrinsicCollarCapAttachmentTransition_source]
      simpa using hPoint
    rw [intrinsicCollarCapAttachmentTransition,
      OpenPartialHomeomorph.trans_source] at hTransitionSource
    simpa [intrinsicCollarCapAttachmentTransition,
      cutOpenCollarAttachmentPartialHomeomorph,
      cutBulkOpenCapInclusionPartialHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
      ((cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).right_inv
        hTransitionSource.2).symm

end
end P0EFTJanusMappingTorusCutBulkCollarCapAttachmentTransition4D
end JanusFormal
