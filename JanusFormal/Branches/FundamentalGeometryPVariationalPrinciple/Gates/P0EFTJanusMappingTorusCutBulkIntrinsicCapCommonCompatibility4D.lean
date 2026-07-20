import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Compatibility of the standard and common intrinsic-cap atlases
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem intrinsicCapStandardToCommon_contMDiff :
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ContMDiff coverModelWithCorners cutCollarModelWithCorners ∞
      (id : CutBulkOpenCap period hPeriod → CutBulkOpenCap period hPeriod) := by
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    (intrinsicCutBulkOpenCap_isManifold period hPeriod).of_le le_top
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  letI : IsManifold cutCollarModelWithCorners ∞ CoverModel :=
    coverModelCutCollar_isManifold
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  intro point
  rw [contMDiffAt_iff_target]
  refine ⟨continuousAt_id, ?_⟩
  let modelPoint : CoverModel := chartAt CoverModel point point
  have hChart : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      (chartAt CoverModel point) point :=
    (contMDiffOn_chart (I := coverModelWithCorners) (x := point))
      |>.contMDiffAt ((chartAt CoverModel point).open_source.mem_nhds
        (mem_chart_source CoverModel point))
  have hModel : ContMDiffAt coverModelWithCorners cutCollarModelWithCorners ∞
      (id : CoverModel → CoverModel) modelPoint :=
    coverModelStandardToCutCollar_contMDiff.contMDiffAt
  have hTarget : ContMDiffAt cutCollarModelWithCorners
      𝓘(Real, CutCollarCoordinates) ∞
      (extChartAt cutCollarModelWithCorners modelPoint) modelPoint :=
    contMDiffAt_extChartAt
  have hComposite := hTarget.comp point (hModel.comp point hChart)
  rw [extChartAt_comp]
  simpa [Function.comp_def, modelPoint] using hComposite

theorem intrinsicCapCommonToStandard_contMDiff :
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (id : CutBulkOpenCap period hPeriod → CutBulkOpenCap period hPeriod) := by
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    (intrinsicCutBulkOpenCap_isManifold period hPeriod).of_le le_top
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  letI : IsManifold cutCollarModelWithCorners ∞ CoverModel :=
    coverModelCutCollar_isManifold
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  intro point
  rw [contMDiffAt_iff_source]
  let modelPoint : CoverModel := chartAt CoverModel point point
  let coordinatePoint : CutCollarCoordinates :=
    extChartAt cutCollarModelWithCorners modelPoint modelPoint
  have hModelInverse : ContMDiffWithinAt
      𝓘(Real, CutCollarCoordinates) cutCollarModelWithCorners ∞
      (extChartAt cutCollarModelWithCorners modelPoint).symm
      (Set.range cutCollarModelWithCorners) coordinatePoint := by
    exact contMDiffWithinAt_extChartAt_symm_range_self modelPoint
  have hModel : ContMDiffAt cutCollarModelWithCorners coverModelWithCorners ∞
      (id : CoverModel → CoverModel) modelPoint :=
    coverModelCutCollarToStandard_contMDiff.contMDiffAt
  have hInverseValue :
      (extChartAt cutCollarModelWithCorners modelPoint).symm coordinatePoint =
        modelPoint := extChartAt_to_inv modelPoint
  have hModel' : ContMDiffAt cutCollarModelWithCorners coverModelWithCorners ∞
      (id : CoverModel → CoverModel)
      ((extChartAt cutCollarModelWithCorners modelPoint).symm coordinatePoint) := by
    rw [hInverseValue]
    exact hModel
  have hMiddle := hModel'.comp_contMDiffWithinAt coordinatePoint hModelInverse
  have hChartInverse : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      (chartAt CoverModel point).symm modelPoint :=
    (contMDiffOn_chart_symm (I := coverModelWithCorners) (x := point))
      |>.contMDiffAt ((chartAt CoverModel point).open_target.mem_nhds
        ((chartAt CoverModel point).map_source
          (mem_chart_source CoverModel point)))
  have hChartInverse' : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      (chartAt CoverModel point).symm
      ((id ∘ (extChartAt cutCollarModelWithCorners modelPoint).symm)
        coordinatePoint) := by
    have hBase :
        (id ∘ (extChartAt cutCollarModelWithCorners modelPoint).symm)
          coordinatePoint = modelPoint := by
      simpa [Function.comp_def] using hInverseValue
    rw [hBase]
    exact hChartInverse
  have hResult := hChartInverse'.comp_contMDiffWithinAt coordinatePoint hMiddle
  rw [extChartAt_comp]
  simpa [Function.comp_def, modelPoint, coordinatePoint] using hResult

end
end P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D
end JanusFormal
