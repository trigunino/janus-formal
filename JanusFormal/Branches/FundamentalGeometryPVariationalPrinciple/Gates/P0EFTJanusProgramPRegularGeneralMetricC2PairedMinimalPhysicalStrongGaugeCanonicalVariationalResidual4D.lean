import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedAugmentedResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D

/-! # Canonical pointwise Maxwell residual in the strong physical system -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedAugmentedResidual4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance intrinsicCanonicalLorentzVolumeMeasureIsOpenPosMeasure :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- The two smooth eight-component residuals derived from the authentic
Maxwell first variations. -/
abbrev RegularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidual :=
  SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber

def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    RegularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidual period
      hPeriod :=
  let plusMetric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    plusBase (point.1.completeVariation.fullMetricPerturbation .plus)
      hPoint.plus_mem
  let minusMetric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    minusBase (point.1.completeVariation.fullMetricPerturbation .minus)
      hPoint.minus_mem
  let plusPotential := regularFrameGaugePotentialFromCoefficients period hPeriod
    plusMetric (configuration.physical.coefficientFields.gauge.1 +
      point.1.completeVariation.independent.gauge.1)
  let minusPotential := regularFrameGaugePotentialFromCoefficients period hPeriod
    minusMetric (configuration.physical.coefficientFields.gauge.2 +
      point.1.completeVariation.independent.gauge.2)
  (regularFrameCanonicalMaxwellVariationalResidual period hPeriod plusMetric
      plusPotential,
    regularFrameCanonicalMaxwellVariationalResidual period hPeriod minusMetric
      minusPotential)

/-- Canonical weak pairing of the two pointwise residuals with independent
physical gauge tests. -/
def regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing
    (residual :
      RegularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidual period
        hPeriod)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) : Real :=
  couplings.plusMaxwellScale *
      smoothGaugeResidualPairing period hPeriod residual.1 test.1
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
    couplings.minusMaxwellScale *
      smoothGaugeResidualPairing period hPeriod residual.2 test.2
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

@[simp] private theorem smoothGaugeResidualPairing_zero_right
    (residual : SmoothQuotientField period hPeriod GaugeFiber) :
    smoothGaugeResidualPairing period hPeriod residual 0
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0 := by
  unfold smoothGaugeResidualPairing
  apply integral_eq_zero_of_ae
  filter_upwards [] with p
  change inner Real (residual p) (0 : GaugeFiber) = 0
  exact inner_zero_right _

@[simp] private theorem smoothGaugeResidualPairing_zero_left
    (direction : SmoothQuotientField period hPeriod GaugeFiber) :
    smoothGaugeResidualPairing period hPeriod 0 direction
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0 := by
  unfold smoothGaugeResidualPairing
  apply integral_eq_zero_of_ae
  filter_upwards [] with p
  change inner Real (0 : GaugeFiber) (direction p) = 0
  exact inner_zero_left _

/-- The total gauge Euler covector is exactly the pairing with the derived
pointwise Maxwell residual pair. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_canonicalVariationalResidualPairing
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point test =
      regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing
        period hPeriod (couplings := couplings)
          (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual
            period hPeriod configuration plusBase minusBase point hPoint) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_weightedMaxwell
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint
        test]
  unfold
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
    regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual
  dsimp only
  rw [canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation,
    canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation,
    intrinsicMaxwellFirstVariation_eq_variationalResidualPairing,
    intrinsicMaxwellFirstVariation_eq_variationalResidualPairing]
  unfold canonicalRegularFrameIntrinsicGaugeResidualPairing
    regularFrameIntrinsicGaugeResidualPairing
  rw [gaugePotentialFrameCoefficients_reconstructed,
    gaugePotentialFrameCoefficients_reconstructed]

/-- Independent nonzero Maxwell couplings make the paired canonical pairing
faithful. -/
theorem regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing_separates
    (residual :
      RegularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidual period
        hPeriod)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    (∀ test : GlobalMinimalPhysicalGaugeTest period hPeriod,
        regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing
          period hPeriod (couplings := couplings) residual test = 0) ↔
      residual = (0, 0) := by
  constructor
  · intro hPairing
    have hPlusPointwise : ∀ p : EffectiveQuotient period hPeriod,
        residual.1 p = 0 :=
      (smoothGaugeField_coupled_pairing_detects_pointwise_zero period hPeriod
        residual.1 (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          couplings.plusMaxwellScale hPlus).mp (by
        intro direction
        simpa only [
          regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing,
          smoothGaugeResidualPairing_zero_right, mul_zero, add_zero] using
            hPairing (direction, 0))
    have hMinusPointwise : ∀ p : EffectiveQuotient period hPeriod,
        residual.2 p = 0 :=
      (smoothGaugeField_coupled_pairing_detects_pointwise_zero period hPeriod
        residual.2 (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          couplings.minusMaxwellScale hMinus).mp (by
        intro direction
        simpa only [
          regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing,
          smoothGaugeResidualPairing_zero_right, mul_zero, zero_add] using
            hPairing (0, direction))
    apply Prod.ext
    · apply SmoothQuotientField.ext period hPeriod GaugeFiber
      exact hPlusPointwise
    · apply SmoothQuotientField.ext period hPeriod GaugeFiber
      exact hMinusPointwise
  · rintro rfl test
    simp only [
      regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing,
      smoothGaugeResidualPairing_zero_left,
      mul_zero, add_zero]

/-- Strong representation whose residual is the actual pair of smooth
pointwise Maxwell Euler fields. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact
    { Residual :=
        RegularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidual
          period hPeriod
      zeroResidual := (0, 0)
      residual :=
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual
          period hPeriod configuration plusBase minusBase point hPoint
      pairing :=
        regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing
          period hPeriod (couplings := couplings)
      represents := fun test ↦
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_canonicalVariationalResidualPairing
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint test
      separates :=
        regularGeneralMetricC2PairedStrongGaugeCanonicalVariationalResidualPairing_separates
          period hPeriod (couplings := couplings)
            (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual
              period hPeriod configuration plusBase minusBase point hPoint)
                hPlus hMinus }

/-- Existing explicit component data with only its gauge coordinate replaced
by the derived smooth pointwise Maxwell residual. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellPDEDataAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint with
    gauge :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus }

def RegularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellSystemAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint hPlus hMinus)

/-- The complete strong physical Euler operator now contains the explicit
pointwise Maxwell residual pair without a supplied Stokes contract. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_canonicalVariationalMaxwellSystem
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint hPlus hMinus)

theorem regular_general_metric_c2_paired_minimal_physical_strong_gauge_canonical_variational_residual_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_canonicalVariationalMaxwellSystem
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase point hPoint hPlus hMinus

end
end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual4D
end JanusFormal
