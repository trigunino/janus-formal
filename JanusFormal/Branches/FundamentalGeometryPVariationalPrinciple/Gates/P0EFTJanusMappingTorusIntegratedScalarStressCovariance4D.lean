import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzScalarStressCovariance4D

/-!
# Integrated diffeomorphism covariance of scalar stress pairings

The intrinsic contravariant scalar stress is paired with two cotangent test
fields and integrated against an arbitrary Borel measure.  Pulling back the
metric, scalar, tests, and measure gives exact pointwise covariance,
integrability transport, and equality of the measured pairing.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntegratedScalarStressCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusGeneralLorentzScalarStressCovariance4D

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

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

/-- A dependent cotangent test field; smoothness is unnecessary for the
measure-transport identity itself. -/
abbrev CotangentTestField :=
  ∀ point : EffectiveQuotient period hPeriod,
    CotangentFiber period hPeriod point

/-- Pullback of a cotangent test field by the genuine derivative. -/
def diffeomorphismCotangentTestPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (test : CotangentTestField period hPeriod) :
    CotangentTestField period hPeriod :=
  fun point => pullbackCovector period hPeriod
    (diffeomorphismDerivative period hPeriod diffeomorphism point)
    (test (diffeomorphism point))

/-- Pointwise scalar stress paired with two cotangent tests. -/
def generalLorentzScalarStressPairingDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (first second : CotangentTestField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  fiberContravariantScalarStress period hPeriod (metric.musical point)
    massSquared (field point)
    (scalarDifferential period hPeriod field point)
    (first point) (second point)

/-- Exact pointwise covariance with both test fields transported. -/
theorem generalLorentzScalarStressPairingDensity_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (first second : CotangentTestField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzScalarStressPairingDensity period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism metric)
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismCotangentTestPullback period hPeriod
          diffeomorphism first)
        (diffeomorphismCotangentTestPullback period hPeriod
          diffeomorphism second) point =
      generalLorentzScalarStressPairingDensity period hPeriod metric
        massSquared field first second (diffeomorphism point) := by
  change fiberContravariantScalarStress period hPeriod
      (pullbackMusical period hPeriod
        (diffeomorphismDerivative period hPeriod diffeomorphism point)
        (metric.musical (diffeomorphism point)))
      massSquared (field (diffeomorphism point))
      (scalarDifferential period hPeriod
        (pullbackSmoothField period hPeriod Real diffeomorphism field) point)
      (pullbackCovector period hPeriod
        (diffeomorphismDerivative period hPeriod diffeomorphism point)
        (first (diffeomorphism point)))
      (pullbackCovector period hPeriod
        (diffeomorphismDerivative period hPeriod diffeomorphism point)
        (second (diffeomorphism point))) = _
  exact holonomicScalarStress_diffeomorphism period hPeriod diffeomorphism
    metric massSquared field point (first (diffeomorphism point))
    (second (diffeomorphism point))

/-- The measured stress pairing against arbitrary cotangent tests. -/
def measuredGeneralLorentzScalarStressPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (first second : CotangentTestField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, generalLorentzScalarStressPairingDensity period hPeriod metric
      massSquared field first second point ∂measure

theorem generalLorentzScalarStressPairingDensity_integrable_iff
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (first second : CotangentTestField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    Integrable
        (generalLorentzScalarStressPairingDensity period hPeriod
          (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
            diffeomorphism metric)
          massSquared
          (pullbackSmoothField period hPeriod Real diffeomorphism field)
          (diffeomorphismCotangentTestPullback period hPeriod
            diffeomorphism first)
          (diffeomorphismCotangentTestPullback period hPeriod
            diffeomorphism second))
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) ↔
      Integrable
        (generalLorentzScalarStressPairingDensity period hPeriod metric
          massSquared field first second) measure := by
  rw [show generalLorentzScalarStressPairingDensity period hPeriod
      (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
        diffeomorphism metric)
      massSquared
      (pullbackSmoothField period hPeriod Real diffeomorphism field)
      (diffeomorphismCotangentTestPullback period hPeriod diffeomorphism first)
      (diffeomorphismCotangentTestPullback period hPeriod diffeomorphism second) =
        generalLorentzScalarStressPairingDensity period hPeriod metric
          massSquared field first second ∘
            (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
              diffeomorphism) by
    funext point
    exact generalLorentzScalarStressPairingDensity_diffeomorphism period
      hPeriod diffeomorphism metric massSquared field first second point]
  exact (diffeomorphismMeasurePullback_measurePreserving period hPeriod
    diffeomorphism measure).integrable_comp_emb
      (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
        diffeomorphism).measurableEmbedding

/-- Integrated stress covariance under simultaneous pullback of all data. -/
theorem measuredGeneralLorentzScalarStressPairing_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (first second : CotangentTestField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    measuredGeneralLorentzScalarStressPairing period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism metric)
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismCotangentTestPullback period hPeriod
          diffeomorphism first)
        (diffeomorphismCotangentTestPullback period hPeriod
          diffeomorphism second)
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      measuredGeneralLorentzScalarStressPairing period hPeriod metric
        massSquared field first second measure := by
  unfold measuredGeneralLorentzScalarStressPairing
  calc
    (∫ point, generalLorentzScalarStressPairingDensity period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism metric)
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismCotangentTestPullback period hPeriod
          diffeomorphism first)
        (diffeomorphismCotangentTestPullback period hPeriod
          diffeomorphism second) point
      ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)) =
      ∫ point, generalLorentzScalarStressPairingDensity period hPeriod metric
          massSquared field first second (diffeomorphism point)
        ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (generalLorentzScalarStressPairingDensity_diffeomorphism period
              hPeriod diffeomorphism metric massSquared field first second)
    _ = _ := (diffeomorphismMeasurePullback_measurePreserving period hPeriod
      diffeomorphism measure).integral_comp'
        (generalLorentzScalarStressPairingDensity period hPeriod metric
          massSquared field first second)

/-- Sum of the measured stress pairings in the two Janus sectors. -/
def measuredGeneralLorentzScalarPairStress
    (firstMetric secondMetric : SmoothGeneralLorentzMetric period hPeriod)
    (firstMassSquared secondMassSquared : Real)
    (firstField secondField : SmoothScalarField period hPeriod)
    (firstLeft firstRight secondLeft secondRight :
      CotangentTestField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  measuredGeneralLorentzScalarStressPairing period hPeriod firstMetric
      firstMassSquared firstField firstLeft firstRight measure +
    measuredGeneralLorentzScalarStressPairing period hPeriod secondMetric
      secondMassSquared secondField secondLeft secondRight measure

/-- Simultaneous finite diffeomorphism transport and sector exchange leave the
two-sector measured stress pairing invariant. -/
theorem measuredGeneralLorentzScalarPairStress_diffeomorphism_exchange
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (firstMetric secondMetric : SmoothGeneralLorentzMetric period hPeriod)
    (firstMassSquared secondMassSquared : Real)
    (firstField secondField : SmoothScalarField period hPeriod)
    (firstLeft firstRight secondLeft secondRight :
      CotangentTestField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    measuredGeneralLorentzScalarPairStress period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism secondMetric)
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism firstMetric)
        secondMassSquared firstMassSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism secondField)
        (pullbackSmoothField period hPeriod Real diffeomorphism firstField)
        (diffeomorphismCotangentTestPullback period hPeriod diffeomorphism
          secondLeft)
        (diffeomorphismCotangentTestPullback period hPeriod diffeomorphism
          secondRight)
        (diffeomorphismCotangentTestPullback period hPeriod diffeomorphism
          firstLeft)
        (diffeomorphismCotangentTestPullback period hPeriod diffeomorphism
          firstRight)
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      measuredGeneralLorentzScalarPairStress period hPeriod
        firstMetric secondMetric firstMassSquared secondMassSquared
        firstField secondField firstLeft firstRight secondLeft secondRight
        measure := by
  unfold measuredGeneralLorentzScalarPairStress
  rw [measuredGeneralLorentzScalarStressPairing_diffeomorphism period hPeriod,
    measuredGeneralLorentzScalarStressPairing_diffeomorphism period hPeriod]
  exact add_comm _ _

end

end P0EFTJanusMappingTorusIntegratedScalarStressCovariance4D
end JanusFormal
