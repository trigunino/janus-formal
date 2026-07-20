import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D

/-!
# Analytic structure on the open cut-throat collar

The open collar inherits the analytic manifold-with-boundary structure of the
finite collar.  Its inclusion into the finite collar is analytic.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The open collar represented as an open subset of the finite collar. -/
def cutThroatOpenCollarOpen :
    TopologicalSpace.Opens (CutThroatFiniteCollar period hPeriod) :=
  ⟨{parameter | parameter.2.1 < 1},
    isOpen_cutThroatOpenCollar period hPeriod⟩

/-- Analytic atlas induced from the finite collar. -/
@[implicit_reducible] def cutThroatOpenCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  change ChartedSpace CutCollarModel
    (cutThroatOpenCollarOpen period hPeriod)
  infer_instance

theorem cutThroatOpenCollar_isManifold :
    @IsManifold Real _ CutCollarCoordinates _ _ CutCollarModel _
      cutCollarModelWithCorners ω (CutThroatOpenCollar period hPeriod) _
      (cutThroatOpenCollarChartedSpace period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
    cutThroatBoundary_isManifold period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ω
      (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollar_isManifold period hPeriod
  change IsManifold cutCollarModelWithCorners ω
    (cutThroatOpenCollarOpen period hPeriod)
  infer_instance

theorem cutThroatOpenCollar_val_contMDiff :
    letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
      cutThroatFiniteCollarChartedSpace period hPeriod
    letI : ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
      cutThroatOpenCollarChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ω
      (fun point : CutThroatOpenCollar period hPeriod => point.1) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
    cutThroatBoundary_isManifold period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ω
      (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollar_isManifold period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
    cutThroatOpenCollarChartedSpace period hPeriod
  change ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ω
    (Subtype.val : cutThroatOpenCollarOpen period hPeriod →
      CutThroatFiniteCollar period hPeriod)
  exact contMDiff_subtype_val

end
end P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
end JanusFormal
