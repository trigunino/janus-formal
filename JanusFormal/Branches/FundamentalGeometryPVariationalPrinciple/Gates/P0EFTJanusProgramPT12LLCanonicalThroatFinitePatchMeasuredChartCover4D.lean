import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatLocalVolumeTransport4D

/-!
# Compact measured-chart refinement of every throat Rellich patch

Each closed throat-generator support is compact.  The explicit shifted
stereographic charts cover it, and normality gives a finite compact
refinement whose pieces stay inside their measured chart domains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchMeasuredChartCover4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusMappingTorusCanonicalThroatLocalVolumeTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData :=
  fixedEquatorData period hPeriod

private abbrev EffectiveThroat :=
  MappingTorus (throatData period hPeriod)

private abbrev StandardSphere :=
  Metric.sphere (0 : EuclideanR3) 1

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

private abbrev Patch :=
  FiniteThroatGeneratorPatch period hPeriod

/-- Finite compact refinement of one closed throat Rellich patch by explicit
measured stereographic chart ranges. -/
structure FiniteThroatGeneratorPatchMeasuredChartCover
    (patch : Patch period hPeriod) where
  charts : Finset (Real × StandardSphere)
  piece :
    (Real × StandardSphere) →
      Set (EffectiveThroat period hPeriod)
  piece_isCompact :
    ∀ chart, IsCompact (piece chart)
  piece_subset_chart :
    ∀ chart,
      piece chart ⊆
        Set.range
          (shiftedThroatInteriorStereographicPhysicalMap
            period hPeriod chart.1 chart.2)
  covers :
    finiteThroatGeneratorClosedPatch period hPeriod patch =
      ⋃ chart ∈ charts, piece chart

/-- Every actual closed throat-generator patch has a finite compact
measured-chart refinement. -/
theorem finiteThroatGeneratorPatchMeasuredChartCover_nonempty
    (patch : Patch period hPeriod) :
    Nonempty (FiniteThroatGeneratorPatchMeasuredChartCover
      period hPeriod patch) := by
  classical
  let support :=
    finiteThroatGeneratorClosedPatch period hPeriod patch
  have hSupportCompact : IsCompact support :=
    finiteThroatGeneratorClosedPatch_isCompact
      period hPeriod patch
  obtain ⟨charts, hChartsCover⟩ :=
    exists_finite_shiftedThroatStereographicChart_cover
      period hPeriod hSupportCompact
  let chartRange :
      (Real × StandardSphere) →
        Set (EffectiveThroat period hPeriod) :=
    fun chart =>
      Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod chart.1 chart.2)
  have hChartOpen :
      ∀ chart ∈ charts, IsOpen (chartRange chart) := by
    intro chart _
    exact
      (shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
        period hPeriod chart.1 chart.2).isOpen_range
  obtain ⟨piece, hPieceCompact, hPieceSubset, hPiecesCover⟩ :=
    hSupportCompact.finite_compact_cover
      charts chartRange hChartOpen hChartsCover
  exact
    ⟨{ charts := charts
       piece := piece
       piece_isCompact := hPieceCompact
       piece_subset_chart := hPieceSubset
       covers := hPiecesCover }⟩

/-- A chosen finite compact measured-chart refinement of the closed
throat-generator patch. -/
def finiteThroatGeneratorPatchMeasuredChartCover
    (patch : Patch period hPeriod) :
    FiniteThroatGeneratorPatchMeasuredChartCover
      period hPeriod patch := by
  exact Classical.choice
    (finiteThroatGeneratorPatchMeasuredChartCover_nonempty
      period hPeriod patch)

end
end P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchMeasuredChartCover4D
end JanusFormal
