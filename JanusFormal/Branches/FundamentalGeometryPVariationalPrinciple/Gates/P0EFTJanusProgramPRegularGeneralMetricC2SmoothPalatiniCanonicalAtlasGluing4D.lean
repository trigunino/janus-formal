import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalFrameDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D

/-! # Canonical-atlas gluing of the smooth Palatini divergence -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCanonicalAtlasGluing4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalDivergenceDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalFrameDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Local representatives of the Palatini divergence agree whenever two
holonomic coordinates represent the same quotient point. -/
theorem regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_on_overlap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (hPoint : first.coordinateMap firstCoordinate =
      second.coordinateMap secondCoordinate) :
    regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
        metric tensor first firstCoordinate =
      regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
        metric tensor second secondCoordinate := by
  rw [regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_smooth,
    regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_smooth, hPoint]

/-- Every quotient point has a representative in the concrete canonical
total atlas whose local divergence is the global smooth divergence there. -/
def CanonicalTotalAtlasPalatiniDivergenceRepresented
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ (canonicalTotalHolonomicAtlasCover period hPeriod).atlasPatches,
      ∃ coordinate : Vector4,
        patch.coordinateMap coordinate = point ∧
          regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
              metric tensor patch coordinate =
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
              tensor point

/-- The concrete canonical total atlas represents the global Palatini
divergence at every point. -/
theorem canonicalTotalAtlasPalatiniDivergenceRepresented
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    CanonicalTotalAtlasPalatiniDivergenceRepresented period hPeriod metric
      tensor := by
  intro point
  rcases canonicalTotalHolonomicAtlasCover_covers period hPeriod point with
    ⟨patch, hPatch, coordinate, hCoordinate⟩
  refine ⟨patch, hPatch, coordinate, hCoordinate, ?_⟩
  rw [regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_smooth,
    hCoordinate]

/-- Gate marker for overlap compatibility and pointwise coverage of the
Palatini divergence on the concrete canonical atlas. -/
theorem regular_general_metric_c2_smooth_palatini_canonical_atlas_gluing_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (∀ (first second : SmoothHolonomicFrameChart4 period hPeriod)
        (firstCoordinate secondCoordinate : Vector4),
      first.coordinateMap firstCoordinate =
          second.coordinateMap secondCoordinate →
        regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
            metric tensor first firstCoordinate =
          regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
            metric tensor second secondCoordinate) ∧
      CanonicalTotalAtlasPalatiniDivergenceRepresented period hPeriod metric
        tensor :=
  ⟨fun first second firstCoordinate secondCoordinate hPoint =>
      regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_on_overlap
        period hPeriod metric tensor first second firstCoordinate
          secondCoordinate hPoint,
    canonicalTotalAtlasPalatiniDivergenceRepresented period hPeriod metric
      tensor⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCanonicalAtlasGluing4D
end JanusFormal
