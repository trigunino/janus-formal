import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCapOverlapExactIntrinsicRange4D

/-!
# Exact intrinsic range of the smooth collar overlap

The collar overlap reaches the same intrinsic open band as the cap overlap,
through the descended tubular diffeomorphism.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCapOverlapExactIntrinsicRange4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The smooth collar overlap mapped to the intrinsic cut bulk. -/
def smoothCutCollarOverlapToCutBulk :
    SmoothCutCollarOverlap period hPeriod →
      PositiveHemisphereCutBulk period hPeriod :=
  smoothCutCapOverlapToCutBulk period hPeriod ∘
    smoothCutCollarCapOverlapDiffeomorph period hPeriod

theorem smoothCutCollarOverlapToCutBulk_isOpenEmbedding :
    IsOpenEmbedding (smoothCutCollarOverlapToCutBulk period hPeriod) := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  exact (smoothCutCapOverlapToCutBulk_isOpenEmbedding period hPeriod).comp
    (smoothCutCollarCapOverlapDiffeomorph period hPeriod).toHomeomorph.isOpenEmbedding

/-- The collar and cap overlap models have the same exact intrinsic image. -/
theorem range_smoothCutCollarOverlapToCutBulk :
    Set.range (smoothCutCollarOverlapToCutBulk period hPeriod) =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹'
        Ioo 0 (Real.sin 1) := by
  rw [← range_smoothCutCapOverlapToCutBulk period hPeriod]
  ext bulk
  constructor
  · rintro ⟨collar, rfl⟩
    exact ⟨smoothCutCollarCapOverlapDiffeomorph period hPeriod collar, rfl⟩
  · rintro ⟨cap, rfl⟩
    obtain ⟨collar, rfl⟩ :=
      (smoothCutCollarCapOverlapDiffeomorph period hPeriod).surjective cap
    exact ⟨collar, rfl⟩

end
end P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D
end JanusFormal
