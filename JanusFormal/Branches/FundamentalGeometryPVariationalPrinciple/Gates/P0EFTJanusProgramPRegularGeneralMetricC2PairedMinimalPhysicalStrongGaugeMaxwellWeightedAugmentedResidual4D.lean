import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellReducedAugmentedResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D

/-! # Weighted Maxwell residual in the full strong PDE system -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedAugmentedResidual4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellReducedAugmentedResidual4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D

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

/-- The authentic gauge residual written with the two canonical weighted
strong Maxwell pairings and their retained boundary divergences. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
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
      canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period
        hPeriod plusMetric plusPotential plusVariation measure +
    couplings.minusMaxwellScale *
      canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral period
        hPeriod minusMetric minusPotential minusVariation measure

omit [IsFiniteMeasure measure] in
/-- The earlier Euler-coefficient residual and the weighted strong residual
are definitionally linked through their common intrinsic first variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual_eq_weighted
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          measure point hPoint test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          measure point hPoint test := by
  unfold
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
  dsimp only
  rw [canonicalRegularMaxwellEulerBoundaryResidualIntegral_eq_intrinsicMaxwellFirstVariation,
    canonicalRegularMaxwellEulerBoundaryResidualIntegral_eq_intrinsicMaxwellFirstVariation,
    canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation,
    canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation]

/-- The total gauge Euler covector is exhausted by the weighted Maxwell
Euler-boundary residual. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_weightedMaxwell
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          measure point hPoint test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_maxwellEulerBoundary
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test,
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual_eq_weighted]

/-- Separating representation with the exact weighted Maxwell gauge
residual. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact
    { Residual := GlobalMinimalPhysicalGaugeTest period hPeriod → Real
      zeroResidual := 0
      residual := fun test ↦
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
          period hPeriod (couplings := couplings) configuration plusBase minusBase
            measure point hPoint test
      pairing := fun residual test ↦ residual test
      represents := fun test ↦
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_weightedMaxwell
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase measure point hPoint test
      separates := by
        constructor
        · intro hZero
          funext test
          exact hZero test
        · intro hZero test
          rw [hZero]
          rfl }

/-- The eight-sector data with its gauge coordinate replaced by the weighted
strong Maxwell residual. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedPDEDataAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellReducedAugmentedPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint with
    gauge :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint }

/-- Complete eight-sector system with the weighted strong Maxwell gauge
coordinate. -/
def RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedSystemAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase measure point hPoint)

/-- Vanishing of the full Euler operator is equivalent to the eight-sector
system containing the exact weighted Maxwell residual. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_spinCSpectralLLFieldGaugeMaxwellWeightedAugmentedSystem
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase measure point hPoint)

/-- Gate marker for the full system with its exact weighted Maxwell gauge
coordinate. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_gauge_maxwell_weighted_augmented_residual_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_spinCSpectralLLFieldGaugeMaxwellWeightedAugmentedSystem
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedAugmentedResidual4D
end JanusFormal
