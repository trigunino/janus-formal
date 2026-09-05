import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDensityDivergence4D

/-!
# Gluing the canonical regular-frame divergence

The intrinsic-density representatives constructed in every holonomic chart
agree on overlaps.  They therefore have a concrete global smooth
representative: the regular-frame anholonomy trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalDensityDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Global smooth field represented by the canonical-density divergence of
the chosen regular-frame vector in every holonomic chart. -/
def regularFrameCanonicalDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) : SmoothScalarField period hPeriod :=
  regularFrameAnholonomyTrace period hPeriod metric vector

/-- Every local intrinsic-density representative is the pullback of the
global canonical regular-frame divergence. -/
theorem regularFrameCanonicalDivergence_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameCanonicalDivergence period hPeriod metric vector
        (patch.coordinateMap coordinate) =
      regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
        metric patch vector coordinate :=
  (regularFrameLocalIntrinsicDensityDivergence_eq_anholonomy period hPeriod
    metric hGauge patch vector coordinate).symm

/-- The two coordinate formulas agree whenever their chart points agree. -/
theorem regularFrameCanonicalDivergence_overlap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) firstPatch)
        metric firstPatch vector firstCoordinate =
      regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) secondPatch)
        metric secondPatch vector secondCoordinate := by
  rw [regularFrameLocalIntrinsicDensityDivergence_eq_anholonomy period hPeriod
      metric hGauge firstPatch vector firstCoordinate,
    regularFrameLocalIntrinsicDensityDivergence_eq_anholonomy period hPeriod
      metric hGauge secondPatch vector secondCoordinate,
    samePoint]

/-- The concrete holonomic atlas supplies a local representative through
every point of the physical quotient. -/
theorem regularFrameCanonicalDivergence_chartThroughEveryPoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (vector : Index4) (point : EffectiveQuotient period hPeriod) :
    ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      patch.coordinateMap coordinate = point ∧
        regularFrameCanonicalDivergence period hPeriod metric vector point =
          regularFrameLocalDensityDivergence period hPeriod
            (localMetricVolumeFactor period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
            metric patch vector coordinate := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  exact ⟨patch, coordinate, hCoordinate,
    hCoordinate ▸ regularFrameCanonicalDivergence_local period hPeriod metric
      hGauge patch vector coordinate⟩

/-- Gate marker for pointwise atlas coverage, overlap compatibility, and the
global smooth representative. -/
theorem regular_frame_canonical_divergence_gluing_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (vector : Index4) :
    (∀ (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
        (firstCoordinate secondCoordinate : Vector4),
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        regularFrameLocalDensityDivergence period hPeriod
            (localMetricVolumeFactor period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) firstPatch)
            metric firstPatch vector firstCoordinate =
          regularFrameLocalDensityDivergence period hPeriod
            (localMetricVolumeFactor period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) secondPatch)
            metric secondPatch vector secondCoordinate) ∧
      (∀ point : EffectiveQuotient period hPeriod,
        ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod)
            (coordinate : Vector4),
          patch.coordinateMap coordinate = point ∧
            regularFrameCanonicalDivergence period hPeriod metric vector point =
              regularFrameLocalDensityDivergence period hPeriod
                (localMetricVolumeFactor period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
                metric patch vector coordinate) := by
  exact ⟨fun firstPatch secondPatch firstCoordinate secondCoordinate =>
      regularFrameCanonicalDivergence_overlap period hPeriod metric hGauge
        firstPatch secondPatch vector firstCoordinate secondCoordinate,
    regularFrameCanonicalDivergence_chartThroughEveryPoint period hPeriod
      metric hGauge vector⟩

end
end P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
end JanusFormal
