import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D

/-!
# Analytic mapping-torus model of the cut-bulk open cap

The strict positive hemisphere is an open analytic submanifold of the unit
three-sphere.  With identity monodromy and doubled period, its mapping torus is
therefore an analytic four-manifold.  This supplies the smooth cap piece of the
future two-open atlas on the cut bulk.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover

variable (period : Real) (hPeriod : period ≠ 0)

/-- Strict positive hemisphere as an open analytic submanifold. -/
def positiveHemisphereInteriorOpen : TopologicalSpace.Opens UnitThreeSphere :=
  ⟨{point | 0 < point.1 0},
    isOpen_lt continuous_const
      ((continuous_apply 0).comp continuous_subtype_val)⟩

local instance positiveHemisphereInteriorOpenLocallyCompactSpace :
    LocallyCompactSpace positiveHemisphereInteriorOpen :=
  positiveHemisphereInteriorOpen.2.locallyCompactSpace

/-- Identity-monodromy doubled-period data for the smooth cap. -/
def cutBulkOpenCapData :
    MappingTorusData positiveHemisphereInteriorOpen where
  monodromy := Homeomorph.refl _
  period := doubledPeriod period
  period_ne_zero := doubledPeriod_ne_zero period hPeriod

abbrev SmoothCutBulkOpenCap :=
  MappingTorus (cutBulkOpenCapData period hPeriod)

@[implicit_reducible] def cutBulkOpenCapCoverChartedSpace :
    ChartedSpace CoverModel
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
  chartedSpacePullback (coverHomeomorphProd
    (cutBulkOpenCapData period hPeriod))

theorem cutBulkOpenCapCover_isManifold :
    @IsManifold Real _ CoverCoordinates _ _ CoverModel _
      coverModelWithCorners ω
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) _
      (cutBulkOpenCapCoverChartedSpace period hPeriod) :=
  isManifold_chartedSpacePullback coverModelWithCorners ω
    (coverHomeomorphProd (cutBulkOpenCapData period hPeriod))

def cutBulkOpenCapProductDeck (winding : Int) :
    positiveHemisphereInteriorOpen × Real →
      positiveHemisphereInteriorOpen × Real :=
  fun point =>
    (point.1, point.2 + (winding : Real) * doubledPeriod period)

theorem cutBulkOpenCapProductDeck_contMDiff (winding : Int) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (cutBulkOpenCapProductDeck period winding) := by
  have hTime : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ω
      (fun time : Real =>
        time + (winding : Real) * doubledPeriod period) :=
    (contDiff_id.add contDiff_const).contMDiff.congr fun _ => rfl
  exact (contMDiff_id : ContMDiff (𝓡 3) (𝓡 3) ω
    (id : positiveHemisphereInteriorOpen →
      positiveHemisphereInteriorOpen)).prodMap hTime

theorem cutBulkOpenCapCover_deck_contMDiff (winding : Int) :
    letI : ChartedSpace CoverModel
        (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (winding +ᵥ · :
        MappingTorusCover (cutBulkOpenCapData period hPeriod) →
          MappingTorusCover (cutBulkOpenCapData period hPeriod)) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (cutBulkOpenCapData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (cutBulkOpenCapData period hPeriod))
  have hComposite := hInv.comp
    ((cutBulkOpenCapProductDeck_contMDiff period winding).comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext
    · change (((Homeomorph.refl
          positiveHemisphereInteriorOpen) ^ winding)
          point.fiber) = point.fiber
      rw [show ((Homeomorph.refl
          positiveHemisphereInteriorOpen) ^ winding)
          point.fiber =
        ((Homeomorph.refl positiveHemisphereInteriorOpen) ^ winding).toEquiv
          point.fiber from rfl,
        homeomorph_toEquiv_zpow]
      rw [show (Homeomorph.refl
          positiveHemisphereInteriorOpen).toEquiv = 1 from rfl,
        one_zpow]
      rfl
    · rfl

@[implicit_reducible] def cutBulkOpenCapQuotientChartedSpace :
    ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  exact mappingTorusSmoothChartedSpace (cutBulkOpenCapData period hPeriod)

theorem smoothCutBulkOpenCap_isManifold :
    @IsManifold Real _ CoverCoordinates _ _ CoverModel _
      coverModelWithCorners ω (SmoothCutBulkOpenCap period hPeriod) _
      (cutBulkOpenCapQuotientChartedSpace period hPeriod) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  exact mappingTorus_isManifold_of_smooth_deck
    coverModelWithCorners ω (cutBulkOpenCapData period hPeriod)
      (cutBulkOpenCapCover_deck_contMDiff period hPeriod)

theorem cutBulkOpenCap_projection_isLocalDiffeomorph :
    letI : ChartedSpace CoverModel
        (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
      cutBulkOpenCapCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (SmoothCutBulkOpenCap period hPeriod) :=
      smoothCutBulkOpenCap_isManifold period hPeriod
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ω
      (mappingTorusMk (cutBulkOpenCapData period hPeriod)) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (cutBulkOpenCapData period hPeriod)) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (SmoothCutBulkOpenCap period hPeriod) :=
    smoothCutBulkOpenCap_isManifold period hPeriod
  exact mappingTorus_projection_isLocalDiffeomorph
    coverModelWithCorners ω (cutBulkOpenCapData period hPeriod)
      (cutBulkOpenCapCover_deck_contMDiff period hPeriod)

end
end P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
end JanusFormal
