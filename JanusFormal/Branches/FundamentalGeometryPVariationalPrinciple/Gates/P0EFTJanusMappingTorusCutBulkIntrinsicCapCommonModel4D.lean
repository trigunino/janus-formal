import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCapCommonModel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D

/-!
# Intrinsic cap atlas in the common collar model
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkCapCommonModel4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The intrinsic cap atlas re-expressed in the collar half-space model. -/
@[implicit_reducible] def intrinsicCutBulkOpenCapCommonChartedSpace :
    ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) := by
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  exact ChartedSpace.comp CutCollarModel CoverModel
    (CutBulkOpenCap period hPeriod)

theorem intrinsicCutBulkOpenCapCommon_isManifold :
    @IsManifold Real _ CutCollarCoordinates _ _ CutCollarModel _
      cutCollarModelWithCorners ∞ (CutBulkOpenCap period hPeriod) _
      (intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod) := by
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  letI : IsManifold cutCollarModelWithCorners ∞ CoverModel :=
    coverModelCutCollar_isManifold
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCap_isManifold period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  refine { StructureGroupoid.HasGroupoid.comp
      (contDiffGroupoid ∞ coverModelWithCorners) ?_ with }
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  have transport
      (f : OpenPartialHomeomorph CoverModel CoverModel)
      (hf : ContMDiffOn coverModelWithCorners coverModelWithCorners ∞
        f f.source) :
      ContMDiffOn cutCollarModelWithCorners cutCollarModelWithCorners ∞
        f f.source := by
    intro point hPoint
    have hMiddle := (hf point hPoint).comp point
      (coverModelCutCollarToStandard_contMDiff point).contMDiffWithinAt
      (by intro source hSource; exact hSource)
    have hResult :=
      (coverModelStandardToCutCollar_contMDiff (f point))
        |>.comp_contMDiffWithinAt point hMiddle
    simpa [Function.comp_def] using hResult
  constructor
  · exact transport e (contMDiffOn_of_mem_contDiffGroupoid he)
  · exact transport e.symm (contMDiffOn_of_mem_contDiffGroupoid
      ((contDiffGroupoid ∞ coverModelWithCorners).symm he))

end
end P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
end JanusFormal
