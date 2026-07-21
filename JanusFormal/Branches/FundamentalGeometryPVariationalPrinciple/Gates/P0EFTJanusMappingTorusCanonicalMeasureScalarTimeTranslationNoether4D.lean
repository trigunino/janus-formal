import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalScalarDiagonalDiffeomorphismNoether4D

/-!
# Scalar time-translation Noether identity with fixed canonical measure

The intrinsic canonical Lorentz volume is fixed by the complete time flow.
Consequently the existing diagonal diffeomorphism invariance of the global
general-Lorentz scalar action specializes to an orbit in which the physical
measure itself is unchanged.  The resulting finite orbit is constant and its
derivative at the identity vanishes.

This remains a single scalar sector.  It supplies neither a local Noether
current nor the metric, Maxwell, ghost, boundary, or full Candidate-A blocks.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalMeasureScalarTimeTranslationNoether4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
open P0EFTJanusMappingTorusGlobalScalarDiagonalDiffeomorphismNoether4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pulling the canonical measure back by a time-flow slice leaves it
literally unchanged. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_timeDiffeomorphism_pullback
    (shift : Real) :
    diffeomorphismMeasurePullback period hPeriod
        (effectiveTimeFlowDiffeomorph period hPeriod shift)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change Measure.map (effectiveTimeFlow period hPeriod (-shift))
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  exact intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_map
    period hPeriod (-shift)

/-- One scalar configuration using the actual intrinsic canonical Lorentz
volume. -/
def canonicalMeasureScalarConfiguration
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    GlobalGeneralLorentzScalarConfiguration period hPeriod where
  metric := metric
  massSquared := massSquared
  field := field
  frame := frame
  measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod

/-- The global scalar action along the complete time-translation orbit, with
the canonical measure held fixed rather than transported as an independent
configuration entry. -/
def fixedCanonicalMeasureScalarTimeOrbit
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (shift : Real) : Real :=
  measuredGeneralLorentzHolonomicScalarAction period hPeriod
    (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod shift) metric)
    massSquared
    (pullbackSmoothField period hPeriod Real
      (effectiveTimeFlowDiffeomorph period hPeriod shift) field)
    (diffeomorphismOrderedTangentVectorPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod shift) frame)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Finite invariance of the actual canonical-measure scalar orbit. -/
theorem fixedCanonicalMeasureScalarTimeOrbit_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (shift : Real) :
    fixedCanonicalMeasureScalarTimeOrbit period hPeriod metric massSquared
        field frame shift =
      sameConfigurationGeneralLorentzScalarAction period hPeriod
        (canonicalMeasureScalarConfiguration period hPeriod metric
          massSquared field frame) := by
  have hInvariant :=
    sameConfigurationGeneralLorentzScalarAction_diagonal_invariant
      period hPeriod (effectiveTimeFlowDiffeomorph period hPeriod shift)
      (canonicalMeasureScalarConfiguration period hPeriod metric
        massSquared field frame)
  simp only [sameConfigurationGeneralLorentzScalarAction,
    diagonalDiffeomorphismPullback, canonicalMeasureScalarConfiguration]
    at hInvariant
  rw [intrinsicCanonicalLorentzVolumeMeasure_timeDiffeomorphism_pullback
    period hPeriod shift] at hInvariant
  simpa [fixedCanonicalMeasureScalarTimeOrbit,
    sameConfigurationGeneralLorentzScalarAction,
    canonicalMeasureScalarConfiguration] using hInvariant

/-- Integrated scalar Noether identity on the fixed physical measure. -/
theorem fixedCanonicalMeasureScalarTimeOrbit_hasDerivAt_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    HasDerivAt
      (fixedCanonicalMeasureScalarTimeOrbit period hPeriod metric massSquared
        field frame) 0 0 := by
  rw [show fixedCanonicalMeasureScalarTimeOrbit period hPeriod metric
      massSquared field frame = fun _ : Real =>
        sameConfigurationGeneralLorentzScalarAction period hPeriod
          (canonicalMeasureScalarConfiguration period hPeriod metric
            massSquared field frame) by
    funext shift
    exact fixedCanonicalMeasureScalarTimeOrbit_eq period hPeriod metric
      massSquared field frame shift]
  exact hasDerivAt_const (x := (0 : Real))
    (c := sameConfigurationGeneralLorentzScalarAction period hPeriod
      (canonicalMeasureScalarConfiguration period hPeriod metric
        massSquared field frame))

theorem fixedCanonicalMeasureScalarTimeOrbit_deriv_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    deriv
      (fixedCanonicalMeasureScalarTimeOrbit period hPeriod metric massSquared
        field frame) 0 = 0 :=
  (fixedCanonicalMeasureScalarTimeOrbit_hasDerivAt_zero period hPeriod metric
    massSquared field frame).deriv

end

end P0EFTJanusMappingTorusCanonicalMeasureScalarTimeTranslationNoether4D
end JanusFormal
