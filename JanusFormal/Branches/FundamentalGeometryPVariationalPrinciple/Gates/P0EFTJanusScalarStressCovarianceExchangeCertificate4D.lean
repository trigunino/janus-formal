import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntegratedScalarStressCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedScalarStressVariation4D

/-!
# Unconditional scalar-stress covariance and exchange certificate

This gate only packages previously proved pointwise, measured, two-sector,
and integrated-variation laws.  It does not assert stress conservation.
-/

namespace JanusFormal
namespace P0EFTJanusScalarStressCovarianceExchangeCertificate4D

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
open P0EFTJanusMappingTorusIntegratedScalarStressCovariance4D
open P0EFTJanusIntegratedScalarStressVariation4D

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

/-- The four already closed covariance and exchange laws, without a local
stress-conservation claim. -/
structure ScalarStressCovarianceExchangeCertificate4D where
  pointwiseGeneralLorentzCovariance :
    ∀ (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
      (metric : SmoothGeneralLorentzMetric period hPeriod)
      (massSquared : Real) (field : SmoothScalarField period hPeriod)
      (point : EffectiveQuotient period hPeriod)
      (first second : CotangentFiber period hPeriod (diffeomorphism point)),
      fiberContravariantScalarStress period hPeriod
          (pullbackMusical period hPeriod
            (diffeomorphismDerivative period hPeriod diffeomorphism point)
            (metric.musical (diffeomorphism point)))
          massSquared (field (diffeomorphism point))
          (scalarDifferential period hPeriod
            (pullbackSmoothField period hPeriod Real diffeomorphism field) point)
          (pullbackCovector period hPeriod
            (diffeomorphismDerivative period hPeriod diffeomorphism point) first)
          (pullbackCovector period hPeriod
            (diffeomorphismDerivative period hPeriod diffeomorphism point) second) =
        fiberContravariantScalarStress period hPeriod
          (metric.musical (diffeomorphism point)) massSquared
          (field (diffeomorphism point))
          (scalarDifferential period hPeriod field (diffeomorphism point))
          first second
  measuredPairingCovariance :
    ∀ (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
      (metric : SmoothGeneralLorentzMetric period hPeriod)
      (massSquared : Real) (field : SmoothScalarField period hPeriod)
      (first second : CotangentTestField period hPeriod)
      (measure : Measure (EffectiveQuotient period hPeriod)),
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
          massSquared field first second measure
  twoSectorDiffeomorphismExchangeCovariance :
    ∀ (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
      (firstMetric secondMetric : SmoothGeneralLorentzMetric period hPeriod)
      (firstMassSquared secondMassSquared : Real)
      (firstField secondField : SmoothScalarField period hPeriod)
      (firstLeft firstRight secondLeft secondRight :
        CotangentTestField period hPeriod)
      (measure : Measure (EffectiveQuotient period hPeriod)),
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
          measure
  integratedStressVariationExchange :
    ∀ {X : Type} [MeasurableSpace X] (measure : Measure X)
      (sectors : TwoScalarMetricSectors4 X),
      integratedTwoSectorScalarStressVariation measure
          (exchangeTwoScalarMetricSectors4 sectors) =
        integratedTwoSectorScalarStressVariation measure sectors

/-- Canonical certificate obtained directly from the four established laws. -/
def scalarStressCovarianceExchangeCertificate :
    ScalarStressCovarianceExchangeCertificate4D period hPeriod where
  pointwiseGeneralLorentzCovariance :=
    holonomicScalarStress_diffeomorphism period hPeriod
  measuredPairingCovariance :=
    measuredGeneralLorentzScalarStressPairing_diffeomorphism period hPeriod
  twoSectorDiffeomorphismExchangeCovariance :=
    measuredGeneralLorentzScalarPairStress_diffeomorphism_exchange period hPeriod
  integratedStressVariationExchange :=
    integratedTwoSectorScalarStressVariation_exchange

/-- The combined covariance/exchange contract is unconditionally inhabited. -/
theorem scalarStressCovarianceExchange_unconditional :
    Nonempty (ScalarStressCovarianceExchangeCertificate4D period hPeriod) :=
  ⟨scalarStressCovarianceExchangeCertificate period hPeriod⟩

end

end P0EFTJanusScalarStressCovarianceExchangeCertificate4D
end JanusFormal
