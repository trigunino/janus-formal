import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D

/-! # Global smooth manifold-with-boundary structure on the cut bulk -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D

set_option autoImplicit false
noncomputable section
local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The preferred two-open atlas makes the cut bulk a smooth four-manifold
with boundary in the common half-space model. -/
theorem cutBulkGlobal_isManifold :
    letI := cutBulkGlobalChartedSpace period hPeriod
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  refine { compatible := ?_ }
  rintro first second ⟨firstPoint, rfl⟩ ⟨secondPoint, rfl⟩
  by_cases hFirst : firstPoint ∈ cutBulkOpenCap period hPeriod
  · by_cases hSecond : secondPoint ∈ cutBulkOpenCap period hPeriod
    · simpa only [cutBulkGlobalChartAt, dif_pos hFirst, dif_pos hSecond] using
        liftedCutBulkCapCapTransition_mem_contDiffGroupoid period hPeriod
          ⟨firstPoint, hFirst⟩ ⟨secondPoint, hSecond⟩
    · simpa only [cutBulkGlobalChartAt, dif_pos hFirst, dif_neg hSecond] using
        liftedCutBulkCapCollarTransition_mem_contDiffGroupoid period hPeriod
          ⟨firstPoint, hFirst⟩
          ((cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm
            secondPoint)
  · by_cases hSecond : secondPoint ∈ cutBulkOpenCap period hPeriod
    · simpa only [cutBulkGlobalChartAt, dif_neg hFirst, dif_pos hSecond] using
        liftedCutBulkCollarCapTransition_mem_contDiffGroupoid period hPeriod
          ((cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm
            firstPoint)
          ⟨secondPoint, hSecond⟩
    · simpa only [cutBulkGlobalChartAt, dif_neg hFirst, dif_neg hSecond] using
        liftedCutBulkCollarCollarTransition_mem_contDiffGroupoid period hPeriod
          ((cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm
            firstPoint)
          ((cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm
            secondPoint)

end
end P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
end JanusFormal
