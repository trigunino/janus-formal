import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D

/-!
# Analytic atlas on the intrinsic cut-bulk open cap

The analytic atlas of the smooth cap mapping torus is pulled back through its
canonical homeomorphism with the intrinsic open cap.  Consequently that
homeomorphism and its inverse are analytic by construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Analytic atlas transported from the smooth cap mapping-torus model. -/
@[implicit_reducible] def intrinsicCutBulkOpenCapChartedSpace :
    ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) := by
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  exact chartedSpacePullback
    (smoothCutBulkOpenCapHomeomorph period hPeriod).symm

theorem intrinsicCutBulkOpenCap_isManifold :
    @IsManifold Real _ CoverCoordinates _ _ CoverModel _
      coverModelWithCorners ω (CutBulkOpenCap period hPeriod) _
      (intrinsicCutBulkOpenCapChartedSpace period hPeriod) := by
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (SmoothCutBulkOpenCap period hPeriod) :=
    smoothCutBulkOpenCap_isManifold period hPeriod
  exact isManifold_chartedSpacePullback coverModelWithCorners ω
    (smoothCutBulkOpenCapHomeomorph period hPeriod).symm

theorem smoothCapHomeomorph_contMDiff :
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (smoothCutBulkOpenCapHomeomorph period hPeriod) := by
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (SmoothCutBulkOpenCap period hPeriod) :=
    smoothCutBulkOpenCap_isManifold period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  exact chartedSpacePullback_invFun_contMDiff coverModelWithCorners ω
    (smoothCutBulkOpenCapHomeomorph period hPeriod).symm

theorem smoothCapHomeomorph_symm_contMDiff :
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (smoothCutBulkOpenCapHomeomorph period hPeriod).symm := by
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (SmoothCutBulkOpenCap period hPeriod) :=
    smoothCutBulkOpenCap_isManifold period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  exact chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
    (smoothCutBulkOpenCapHomeomorph period hPeriod).symm

end
end P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
end JanusFormal
