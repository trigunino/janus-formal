import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D

/-!
# Compact measured-chart refinement of every Rellich patch

Each closed partition support is compact.  The explicit shifted
stereographic charts cover it, and normality gives a finite compact
refinement whose pieces stay inside their measured chart domains.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchMeasuredChartCover4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData :=
  reflectedSphereData period hPeriod

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

private abbrev StandardSphere :=
  Metric.sphere (0 : EuclideanR4) 1

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

private abbrev Patch :=
  FiniteTangentGeneratorPatch period hPeriod

/-- Finite compact refinement of one closed Rellich patch by explicit
measured stereographic chart ranges. -/
structure FiniteTangentPatchMeasuredChartCover
    (patch : Patch period hPeriod) where
  charts : Finset (Real × StandardSphere)
  piece :
    (Real × StandardSphere) →
      Set (EffectiveQuotient period hPeriod)
  piece_isCompact :
    ∀ chart, IsCompact (piece chart)
  piece_subset_chart :
    ∀ chart,
      piece chart ⊆
        Set.range
          (shiftedCanonicalInteriorStereographicPhysicalMap
            period hPeriod chart.1 chart.2)
  covers :
    finiteTangentGeneratorClosedPatch period hPeriod patch =
      ⋃ chart ∈ charts, piece chart

/-- Every actual closed tangent-generator patch has a finite compact
measured-chart refinement. -/
theorem finiteTangentPatchMeasuredChartCover_nonempty
    (patch : Patch period hPeriod) :
    Nonempty (FiniteTangentPatchMeasuredChartCover
      period hPeriod patch) := by
  classical
  let support :=
    finiteTangentGeneratorClosedPatch period hPeriod patch
  have hSupportCompact : IsCompact support :=
    (finiteTangentGeneratorClosedPatch_isClosed
      period hPeriod patch).isCompact
  obtain ⟨charts, hChartsCover⟩ :=
    exists_finite_shiftedStereographicChart_cover
      period hPeriod hSupportCompact
  let chartRange :
      (Real × StandardSphere) →
        Set (EffectiveQuotient period hPeriod) :=
    fun chart =>
      Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod chart.1 chart.2)
  have hChartOpen :
      ∀ chart ∈ charts, IsOpen (chartRange chart) := by
    intro chart _
    exact
      (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
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
tangent-generator patch. -/
def finiteTangentPatchMeasuredChartCover
    (patch : Patch period hPeriod) :
    FiniteTangentPatchMeasuredChartCover
      period hPeriod patch := by
  exact Classical.choice
    (finiteTangentPatchMeasuredChartCover_nonempty
      period hPeriod patch)

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchMeasuredChartCover4D
end JanusFormal
