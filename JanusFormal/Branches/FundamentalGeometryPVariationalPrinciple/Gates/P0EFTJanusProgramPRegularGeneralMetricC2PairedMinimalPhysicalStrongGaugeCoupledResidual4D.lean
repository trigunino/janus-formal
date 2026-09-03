import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D

/-! # Exact coupled residual of the strong gauge equation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledResidual4D

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

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
variable (measure : Measure (EffectiveQuotient period hPeriod))
variable [IsFiniteMeasure measure]
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- All non-Maxwell contributions to the authentic strong gauge equation. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) : Real :=
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let blocks := regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
    period hPeriod configuration.physical couplings data plusBase minusBase hBase
      measure
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test
  (((((actionGradient blocks.candidateA point direction +
    actionGradient blocks.matter point direction) +
    actionGradient blocks.robin point direction) +
    actionGradient blocks.ll point direction) +
    actionGradient blocks.einsteinHilbertPlus point direction) +
    actionGradient blocks.einsteinHilbertMinus point direction) +
    actionGradient blocks.finiteBV point direction

/-- Exact scalar weak residual on a paired strong gauge test. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) : Real :=
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
  let plusVariation := regularFrameGaugePotentialFromCoefficients period hPeriod
    plusMetric test.1
  let minusVariation := regularFrameGaugePotentialFromCoefficients period hPeriod
    minusMetric test.2
  couplings.plusMaxwellScale *
      intrinsicMaxwellFirstVariation period hPeriod plusMetric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod plusMetric
          plusPotential plusVariation) measure +
    couplings.minusMaxwellScale *
      intrinsicMaxwellFirstVariation period hPeriod minusMetric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod minusMetric
          minusPotential minusVariation) measure +
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point test

/-- The total strong gauge covector is the two explicit Maxwell weak
variations plus the exact remainder of every other action block. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_gauge_coupled_residual_gate
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
          measure point test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let blocks := regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
    period hPeriod configuration.physical couplings data plusBase minusBase hBase
      measure
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test
  have hTotal :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkEuler_restrict_apply_eq_nineBlockSum
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint
          (globalMinimalPhysicalGaugeTestInclusion period hPeriod) test
  change regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point test =
    fullCoupledEulerBlockSum blocks point direction at hTotal
  rw [hTotal]
  have hMaxwell :=
    regular_general_metric_c2_paired_minimal_physical_strong_maxwell_weak_first_variation_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test
  unfold regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
  dsimp only at hMaxwell ⊢
  change actionGradient blocks.maxwellPlus point direction = _ ∧
    actionGradient blocks.maxwellMinus point direction = _ at hMaxwell
  unfold fullCoupledEulerBlockSum
  simp only [add_apply]
  rw [hMaxwell.1, hMaxwell.2]
  unfold regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
  dsimp only
  ring

/-- Strong gauge stationarity is exactly vanishing of the coupled weak
Maxwell residual on every paired gauge test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_zero_iff_weakCoupledResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          measure point = 0 ↔
      ∀ test : GlobalMinimalPhysicalGaugeTest period hPeriod,
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint test = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  constructor
  · intro hStationary test
    rw [← regular_general_metric_c2_paired_minimal_physical_strong_gauge_coupled_residual_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    rw [hStationary]
    rfl
  · intro hResidual
    apply LinearMap.ext
    intro test
    rw [regular_general_metric_c2_paired_minimal_physical_strong_gauge_coupled_residual_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    simpa using hResidual test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledResidual4D
end JanusFormal
