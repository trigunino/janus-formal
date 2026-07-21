import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryOpenCollarFace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutOpenCollarGlobalSmooth4D

/-! # Smoothness of the global cut-boundary inclusion -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryGlobalSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBoundaryOpenCollarFace4D
open P0EFTJanusMappingTorusCutOpenCollarGlobalSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical throat inclusion is smooth for the global cut-bulk atlas. -/
theorem cutBoundaryInclusion_contMDiff :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatFiniteCollarChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := cutBulkGlobalChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners cutCollarModelWithCorners ∞
      (cutBoundaryInclusion period hPeriod) := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI := cutBulkGlobalChartedSpace period hPeriod
  have hComposition :=
    (cutOpenCollarAttachment_contMDiff period hPeriod).comp
      (contMDiff_cutBoundaryOpenCollarFace period hPeriod)
  simpa only [Function.comp_def,
    cutOpenCollarAttachment_cutBoundaryOpenCollarFace] using hComposition

end
end P0EFTJanusMappingTorusCutBoundaryGlobalSmooth4D
end JanusFormal
