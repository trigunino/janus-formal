import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-! # Local Euclidean Rellich core on the actual LL throat -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-- Hilbert coordinate presentation of the three-dimensional throat chart. -/
abbrev CanonicalThroatChartHilbertCoordinates :=
  EuclideanSpace Real (Fin 3)

local instance canonicalThroatChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalThroatChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl

/-- Fixed continuous linear identification with the throat product chart. -/
def canonicalThroatChartHilbertEquivCoverCoordinates :
    CanonicalThroatChartHilbertCoordinates ≃L[Real]
      ThroatCoverCoordinates :=
  (LinearEquiv.ofFinrankEq
    CanonicalThroatChartHilbertCoordinates ThroatCoverCoordinates (by
      simp [CanonicalThroatChartHilbertCoordinates,
        ThroatCoverCoordinates]))
    |>.toContinuousLinearEquiv

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Image of one actual closed throat partition support in its preferred
three-dimensional chart. -/
def finiteThroatGeneratorPatchCoordinateSupport
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Set ThroatCoverCoordinates :=
  extChartAt throatCoverModelWithCorners patch.1 ''
    finiteThroatGeneratorClosedPatch period hPeriod patch

theorem finiteThroatGeneratorPatchCoordinateSupport_isCompact
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsCompact
      (finiteThroatGeneratorPatchCoordinateSupport
        period hPeriod patch) := by
  apply
    (finiteThroatGeneratorClosedPatch_isCompact
      period hPeriod patch).image_of_continuousOn
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

theorem finiteThroatGeneratorPatchCoordinateSupport_measurable
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    MeasurableSet
      (finiteThroatGeneratorPatchCoordinateSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchCoordinateSupport_isCompact
    period hPeriod patch).isClosed.measurableSet

/-- The same compact support in the Euclidean Hilbert presentation. -/
def finiteThroatGeneratorPatchHilbertSupport
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Set CanonicalThroatChartHilbertCoordinates :=
  canonicalThroatChartHilbertEquivCoverCoordinates.symm ''
    finiteThroatGeneratorPatchCoordinateSupport period hPeriod patch

theorem finiteThroatGeneratorPatchHilbertSupport_isCompact
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsCompact
      (finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchCoordinateSupport_isCompact
    period hPeriod patch).image
      canonicalThroatChartHilbertEquivCoverCoordinates.symm.continuous

theorem finiteThroatGeneratorPatchHilbertSupport_measurable
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    MeasurableSet
      (finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchHilbertSupport_isCompact
    period hPeriod patch).isClosed.measurableSet

/-- Supported scalar Euclidean `H¹` attached to one actual throat patch. -/
abbrev FiniteThroatGeneratorPatchEuclideanH1
    (patch : FiniteThroatGeneratorPatch period hPeriod) :=
  ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On
    (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch))

/-- Ambient scalar `L²` on the three-dimensional Euclidean model. -/
abbrev FiniteThroatGeneratorPatchEuclideanL2 :=
  CanonicalThroatChartHilbertCoordinates →₂[
    (volume : Measure CanonicalThroatChartHilbertCoordinates)] Real

/-- Local supported `H¹ → L²` inclusion for one actual throat patch. -/
def finiteThroatGeneratorPatchEuclideanRellichEmbedding
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch →L[Real]
      FiniteThroatGeneratorPatchEuclideanL2 :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2
    (E := CanonicalThroatChartHilbertCoordinates)
    (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch)

/-- Euclidean Rellich compactness on every selected actual throat patch. -/
theorem finiteThroatGeneratorPatchEuclideanRellichEmbedding_isCompact
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsCompactOperator
      (finiteThroatGeneratorPatchEuclideanRellichEmbedding
        period hPeriod patch) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2
    (finiteThroatGeneratorPatchHilbertSupport_isCompact
      period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch)

end
end P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
end JanusFormal
