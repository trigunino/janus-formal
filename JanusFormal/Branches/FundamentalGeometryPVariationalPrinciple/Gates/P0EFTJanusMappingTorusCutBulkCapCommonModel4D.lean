import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkInteriorModelDiffeomorph4D

/-!
# The cap model expressed in the cut-collar half-space model
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCapCommonModel4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkInteriorModelDiffeomorph4D

/-- The Euclidean cap model, recharted by the interior of the collar's
half-space model. -/
@[implicit_reducible] def coverModelCutCollarChartedSpace :
    ChartedSpace CutCollarModel CoverModel := by
  letI : ChartedSpace CutCollarModel cutCollarModelInteriorOpen :=
    inferInstance
  exact chartedSpacePullback
    coverModelCutCollarInteriorDiffeomorph.toHomeomorph

theorem coverModelCutCollar_isManifold :
    @IsManifold Real _ CutCollarCoordinates _ _ CutCollarModel _
      cutCollarModelWithCorners ∞ CoverModel _
      coverModelCutCollarChartedSpace := by
  letI : ChartedSpace CutCollarModel cutCollarModelInteriorOpen :=
    inferInstance
  letI : IsManifold cutCollarModelWithCorners ∞
      cutCollarModelInteriorOpen := inferInstance
  exact isManifold_chartedSpacePullback cutCollarModelWithCorners ∞
    coverModelCutCollarInteriorDiffeomorph.toHomeomorph

theorem coverModelCutCollarDiffeomorph_contMDiff :
    letI : ChartedSpace CutCollarModel CoverModel :=
      coverModelCutCollarChartedSpace
    ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ∞
      coverModelCutCollarInteriorDiffeomorph := by
  letI : ChartedSpace CutCollarModel cutCollarModelInteriorOpen :=
    inferInstance
  letI : IsManifold cutCollarModelWithCorners ∞
      cutCollarModelInteriorOpen := inferInstance
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  exact chartedSpacePullback_toFun_contMDiff cutCollarModelWithCorners ∞
    coverModelCutCollarInteriorDiffeomorph.toHomeomorph

theorem coverModelCutCollarDiffeomorph_symm_contMDiff :
    letI : ChartedSpace CutCollarModel CoverModel :=
      coverModelCutCollarChartedSpace
    ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ∞
      coverModelCutCollarInteriorDiffeomorph.symm := by
  letI : ChartedSpace CutCollarModel cutCollarModelInteriorOpen :=
    inferInstance
  letI : IsManifold cutCollarModelWithCorners ∞
      cutCollarModelInteriorOpen := inferInstance
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  exact chartedSpacePullback_invFun_contMDiff cutCollarModelWithCorners ∞
    coverModelCutCollarInteriorDiffeomorph.toHomeomorph

/-- Identity from the standard Euclidean atlas to the common collar-model
atlas. -/
theorem coverModelStandardToCutCollar_contMDiff :
    letI : ChartedSpace CutCollarModel CoverModel :=
      coverModelCutCollarChartedSpace
    ContMDiff coverModelWithCorners cutCollarModelWithCorners ∞
      (id : CoverModel → CoverModel) := by
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  exact ((coverModelCutCollarDiffeomorph_symm_contMDiff).comp
    coverModelToCutCollarInterior_contMDiff).congr fun _ =>
      (coverModelToCutCollarInterior_leftInverse _).symm

/-- Identity from the common collar-model atlas back to the standard
Euclidean atlas. -/
theorem coverModelCutCollarToStandard_contMDiff :
    letI : ChartedSpace CutCollarModel CoverModel :=
      coverModelCutCollarChartedSpace
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (id : CoverModel → CoverModel) := by
  letI : ChartedSpace CutCollarModel CoverModel :=
    coverModelCutCollarChartedSpace
  exact (cutCollarInteriorToCoverModel_contMDiff.comp
    coverModelCutCollarDiffeomorph_contMDiff).congr fun _ =>
      (coverModelToCutCollarInterior_leftInverse _).symm

end
end P0EFTJanusMappingTorusCutBulkCapCommonModel4D
end JanusFormal
