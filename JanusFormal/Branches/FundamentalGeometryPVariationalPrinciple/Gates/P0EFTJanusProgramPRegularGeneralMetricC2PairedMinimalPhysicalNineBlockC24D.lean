import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D

/-! # Nine physical C² blocks in the strong paired minimal chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D

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

/-- Forget the LL coordinate while retaining the old metric-gauge core. -/
def globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod
        plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
    configuration.physical plusBase minusBase).mkContinuous 1 (by
      intro direction
      rw [one_mul]
      change
        ‖globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration.physical plusBase minusBase direction‖ ≤
          ‖(globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration
              direction,
            (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization direction,
              (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                  data analysis direction,
                (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                    configuration.physical plusBase minusBase direction,
                  globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                    configuration.physical
                      (canonicalDivergenceFreeLLFrame period hPeriod)
                        direction))))‖
      calc
        _ ≤ ‖(globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
              configuration.physical plusBase minusBase direction,
            globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
              configuration.physical
                (canonicalDivergenceFreeLLFrame period hPeriod) direction)‖ :=
          norm_fst_le _
        _ ≤ ‖(globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
              data analysis direction,
            (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                configuration.physical plusBase minusBase direction,
              globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                  configuration.physical
                    (canonicalDivergenceFreeLLFrame period hPeriod) direction))‖ :=
          norm_snd_le
            (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                data analysis direction,
              (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                  configuration.physical plusBase minusBase direction,
                globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                  configuration.physical
                    (canonicalDivergenceFreeLLFrame period hPeriod) direction))
        _ ≤ ‖(globalMinimalPhysicalMatterGraphLinearMap period hPeriod
              configuration couplings.matterMassSquared realization direction,
            (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                data analysis direction,
              (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                  configuration.physical plusBase minusBase direction,
                globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                  configuration.physical
                    (canonicalDivergenceFreeLLFrame period hPeriod) direction)))‖ :=
          norm_snd_le
            (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization direction,
              (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                  data analysis direction,
                (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                    configuration.physical plusBase minusBase direction,
                  globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                    configuration.physical
                      (canonicalDivergenceFreeLLFrame period hPeriod) direction)))
        _ ≤ ‖(globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration
              direction,
            (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization direction,
              (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                  data analysis direction,
                (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                    configuration.physical plusBase minusBase direction,
                  globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                    configuration.physical
                      (canonicalDivergenceFreeLLFrame period hPeriod)
                        direction))))‖ :=
          norm_snd_le
            (globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration
                direction,
              (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                  configuration couplings.matterMassSquared realization direction,
                (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                    data analysis direction,
                  (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period
                      hPeriod configuration.physical plusBase minusBase direction,
                    globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
                      configuration.physical
                        (canonicalDivergenceFreeLLFrame period hPeriod)
                          direction))))
      )

/-- Strong continuous projection to the paired relative metric core. -/
def globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase
        minusBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact (ContinuousLinearMap.fst Real
    (RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase)
    (RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod)).comp
      (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase)

/-- Strong continuous projection to the primitive-matter graph coordinate. -/
def globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact globalMinimalPhysicalMatterLLExtraGraphMatterCLM period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricGaugeLLStrongCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase
          (canonicalDivergenceFreeLLFrame period hPeriod))

@[simp] theorem globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase direction =
      globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase direction :=
  rfl

@[simp] theorem globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase direction =
      globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase direction :=
  rfl

@[simp] theorem globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase direction =
      globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization direction :=
  rfl

/-- The interaction block remains C² after strengthening by the LL first jet. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_candidateA_strong_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hAux : ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase
          minusBase measure couplings.interactionScale
            couplings.interactionCoefficients
            (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period
              hPeriod configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :=
    (regularGeneralMetricC2PairedInteractionC2Action_contDiffOn period hPeriod
      plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients).comp
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
      (fun direction hDirection =>
        (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase direction).1
            hDirection)
  exact (hAux.contDiffWithinAt hPoint).congr_of_mem
    (fun direction hDirection => by
      simpa using
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection))
    hPoint

/-- Both Einstein--Hilbert blocks remain C² in the strong chart. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_einsteinHilbert_strong_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).einsteinHilbertPlus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point ∧
      ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).einsteinHilbertMinus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hMap : ContDiffOn Real 2
      (fun direction : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical =>
        globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
          configuration data analysis realization plusBase minusBase direction)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :=
    (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
  have hImage : ∀ direction,
      direction ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
          period hPeriod configuration.physical plusBase minusBase →
        globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
            configuration data analysis realization plusBase minusBase direction ∈
          regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase
            minusBase := fun direction hDirection =>
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase direction).1
          hDirection
  have hPlus :=
    ((regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.plusEinstein).comp
        hMap hImage).contDiffWithinAt hPoint
  have hMinus :=
    ((regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.minusEinstein).comp
        hMap hImage).contDiffWithinAt hPoint
  exact ⟨
    hPlus.congr_of_mem (fun direction hDirection => by
      simpa using
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection)) hPoint,
    hMinus.congr_of_mem (fun direction hDirection => by
      simpa using
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection)) hPoint⟩

/-- Both Maxwell blocks remain C² in the strong chart. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_maxwell_strong_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).maxwellPlus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point ∧
      ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).maxwellMinus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hMap : ContDiffOn Real 2
      (fun direction : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical =>
        globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
          configuration data analysis realization plusBase minusBase direction)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :=
    (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
      configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
  have hImage : ∀ direction,
      direction ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
          period hPeriod configuration.physical plusBase minusBase →
        globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase direction ∈
          regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
            plusBase minusBase := fun direction hDirection =>
      ⟨(globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase direction).1
          hDirection, Set.mem_univ _⟩
  have hPlusAux : ContDiffWithinAt Real 2
      (fun direction => couplings.plusMaxwellScale *
        regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
          configuration.physical plusBase minusBase measure
            (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period
              hPeriod configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (contDiffOn_const.mul
      ((regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_contDiffOn_two
        period hPeriod configuration.physical plusBase minusBase measure).comp
          hMap hImage)).contDiffWithinAt hPoint
  have hMinusAux : ContDiffWithinAt Real 2
      (fun direction => couplings.minusMaxwellScale *
        regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
          configuration.physical plusBase minusBase measure
            (globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period
              hPeriod configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (contDiffOn_const.mul
      ((regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_contDiffOn_two
        period hPeriod configuration.physical plusBase minusBase measure).comp
          hMap hImage)).contDiffWithinAt hPoint
  exact ⟨
    hPlusAux.congr_of_mem (fun direction hDirection => by
      simpa using
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection)) hPoint,
    hMinusAux.congr_of_mem (fun direction hDirection => by
      simpa using
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection)) hPoint⟩

/-- The translated primitive-matter block remains C² in the strong chart. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_matter_strong_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).matter
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hInput : ContDiff Real 2
      (fun direction : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical =>
        realization.toGraph configuration.physical.spinCMatter +
          globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
            configuration data analysis realization plusBase minusBase direction) :=
    contDiff_const.add
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff
  have hAction : ContDiff Real 2
      (fun direction : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical =>
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (realization.toGraph configuration.physical.spinCMatter +
            globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
              configuration data analysis realization plusBase minusBase
                direction)) :=
    (programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
      couplings.matterMassSquared).comp hInput
  exact hAction.contDiffWithinAt.congr_of_mem
    (fun direction hDirection => by
      simpa [regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput] using
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_eq
          period hPeriod configuration data realization plusBase minusBase hBase
            measure direction hDirection))
    hPoint

/-- All nine genuine physical action blocks are C² in one strong topology. -/
def regularGeneralMetricC2PairedMinimalPhysicalNineBlockC2WithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    FullCoupledC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hEinstein :=
    regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_einsteinHilbert_strong_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint
  have hMaxwell :=
    regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_maxwell_strong_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint
  exact
    { candidateA :=
        regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_candidateA_strong_contDiffWithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint
      matter :=
        regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_matter_strong_contDiffWithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint
      robin :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_contDiffWithinAt
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure point hPoint
      ll :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_contDiffWithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint
      einsteinHilbertPlus := hEinstein.1
      einsteinHilbertMinus := hEinstein.2
      maxwellPlus := hMaxwell.1
      maxwellMinus := hMaxwell.2
      finiteBV :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_contDiffWithinAt
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure point hPoint }

/-- Gate marker: the complete nine-block physical action is jointly C². -/
theorem regular_general_metric_c2_paired_minimal_physical_nine_block_c2_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    FullCoupledC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
  regularGeneralMetricC2PairedMinimalPhysicalNineBlockC2WithinAt period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure point
      hPoint

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
end JanusFormal
