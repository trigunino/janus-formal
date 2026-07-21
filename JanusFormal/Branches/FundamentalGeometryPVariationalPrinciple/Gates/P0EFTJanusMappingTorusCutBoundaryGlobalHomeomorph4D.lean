import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryClosedEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalBoundary4D

/-! # Canonical homeomorphism onto the global cut-bulk boundary -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBoundaryClosedEmbedding4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The orientation-double throat parametrizes exactly the intrinsic manifold
boundary of the global cut bulk. -/
def cutBoundaryGlobalBoundaryHomeomorph :
    letI := cutBulkGlobalChartedSpace period hPeriod
    CutThroatBoundary period hPeriod ≃ₜ
      ↑(cutCollarModelWithCorners.boundary
        (PositiveHemisphereCutBulk period hPeriod)) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact (cutBoundaryInclusion_isClosedEmbedding period hPeriod).isEmbedding
    |>.toHomeomorph |>.trans
      (Homeomorph.setCongr
        (cutBulkGlobal_boundary_eq_range_cutBoundaryInclusion
          period hPeriod).symm)

@[simp] theorem cutBoundaryGlobalBoundaryHomeomorph_apply
    (boundary : CutThroatBoundary period hPeriod) :
    letI := cutBulkGlobalChartedSpace period hPeriod
    (cutBoundaryGlobalBoundaryHomeomorph period hPeriod boundary).1 =
      cutBoundaryInclusion period hPeriod boundary := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  rfl

end
end P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D
end JanusFormal
