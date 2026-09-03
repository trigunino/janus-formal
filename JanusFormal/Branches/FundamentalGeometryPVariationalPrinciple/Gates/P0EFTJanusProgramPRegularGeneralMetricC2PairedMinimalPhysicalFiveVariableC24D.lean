import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

/-! # Five variable physical C² blocks on the joint paired graph -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalFiveVariableC24D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Openness of the exact paired domain in the joint metric-gauge graph topology. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_joint_isOpen
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    IsOpen
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  rw [← regularGeneralMetricC2PairedMinimalPhysicalOpenAdmissibleDomain_eq
    period hPeriod configuration.physical plusBase minusBase]
  change IsOpen
    ((globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase) ⁻¹'
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
  exact
    (regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen
      period hPeriod plusBase minusBase).preimage
      (globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase).continuous

/-- The interaction auxiliary action remains C² for the stronger joint graph. -/
theorem regularGeneralMetricC2PairedInteractionC2Action_joint_projected_contDiffOn
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
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase
          minusBase measure couplings.interactionScale
            couplings.interactionCoefficients
            (globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
              configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact (regularGeneralMetricC2PairedInteractionC2Action_contDiffOn period hPeriod
      plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients).comp
    (globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
    (fun direction hDirection =>
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase direction).1
          hDirection)

/-- The genuine interaction block is C² for the joint metric-gauge topology. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_candidateA_joint_contDiffWithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hAux :=
    (regularGeneralMetricC2PairedInteractionC2Action_joint_projected_contDiffOn
      period hPeriod configuration data analysis realization plusBase minusBase
        measure).contDiffWithinAt hPoint
  exact hAux.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection)
    hPoint

/-- Both Einstein--Hilbert auxiliary actions remain C² for the joint graph. -/
theorem regularGeneralMetricC2PairedEinsteinHilbertAction_joint_projected_contDiffOn
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
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
        (fun direction =>
          regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
            period hPeriod plusBase minusBase measure couplings.plusEinstein
              (globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
                configuration data analysis realization plusBase minusBase
                  direction))
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) ∧
      ContDiffOn Real 2
        (fun direction =>
          regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
            period hPeriod plusBase minusBase measure couplings.minusEinstein
              (globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
                configuration data analysis realization plusBase minusBase
                  direction))
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hMap : ContDiffOn Real 2
      (fun direction : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical =>
        globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
          configuration data analysis realization plusBase minusBase direction)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :=
    (globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
  have hImage : ∀ direction,
      direction ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
          period hPeriod configuration.physical plusBase minusBase →
        globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM period hPeriod
            configuration data analysis realization plusBase minusBase direction ∈
          regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
            plusBase minusBase := fun direction hDirection =>
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase direction).1
          hDirection
  exact ⟨
    (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.plusEinstein).comp
        hMap hImage,
    (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.minusEinstein).comp
        hMap hImage⟩

/-- The two genuine Einstein--Hilbert blocks are C² for the joint graph. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_einsteinHilbert_joint_contDiffWithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
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
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hAux := regularGeneralMetricC2PairedEinsteinHilbertAction_joint_projected_contDiffOn
    period hPeriod configuration data analysis realization plusBase minusBase
      measure
  exact ⟨
    (hAux.1.contDiffWithinAt hPoint).congr_of_mem
      (fun direction hDirection =>
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection)
      hPoint,
    (hAux.2.contDiffWithinAt hPoint).congr_of_mem
      (fun direction hDirection =>
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_eq
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure direction hDirection)
      hPoint⟩

/-- All five nonconstant physical blocks share one joint C² topology. -/
def regularGeneralMetricC2PairedMinimalPhysicalFiveVariableC2WithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    GlobalCandidateAFiveVariablePhysicalC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hEinstein :=
    regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_einsteinHilbert_joint_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint
  exact
    { candidateA :=
        regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_candidateA_joint_contDiffWithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint
      einsteinHilbertPlus := hEinstein.1
      einsteinHilbertMinus := hEinstein.2
      maxwellPlus :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_contDiffWithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint
      maxwellMinus :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_contDiffWithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint }

/-- Adding the two constant boundary blocks gives all seven physical blocks. -/
def regularGeneralMetricC2PairedMinimalPhysicalSevenPhysicalC2WithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    GlobalCandidateASevenPhysicalC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact regularGeneralMetricC2PairedMinimalPhysicalFiveVariableC2ToSevenPhysical
    period hPeriod configuration.physical couplings data plusBase minusBase hBase
      measure point hPoint
      (regularGeneralMetricC2PairedMinimalPhysicalFiveVariableC2WithinAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint)

/-- Gate marker: the seven physical Candidate-A blocks are jointly C². -/
theorem regular_general_metric_c2_paired_minimal_physical_seven_block_c2_gate
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    GlobalCandidateASevenPhysicalC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
  regularGeneralMetricC2PairedMinimalPhysicalSevenPhysicalC2WithinAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalFiveVariableC24D
end JanusFormal
