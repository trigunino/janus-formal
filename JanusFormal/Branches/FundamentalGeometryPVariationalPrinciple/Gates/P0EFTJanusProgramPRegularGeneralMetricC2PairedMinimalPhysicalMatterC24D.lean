import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalFiveVariableC24D

/-! # Primitive matter C² on the paired minimal-physical chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

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

/-- Matter graph projection for the joint metric-gauge graph norm. -/
def globalMinimalPhysicalPairedMetricGaugeCoreMatterCLM
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
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
    couplings.matterMassSquared realization).mkContinuous 1 (by
      intro direction
      rw [one_mul]
      change
        ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
            couplings.matterMassSquared realization direction‖ ≤
          ‖(globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration
              direction,
            (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization direction,
              (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                  data analysis direction,
                globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                  configuration.physical plusBase minusBase direction)))‖
      exact
        (norm_fst_le
          (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
              configuration couplings.matterMassSquared realization direction,
            (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                data analysis direction,
              globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
                configuration.physical plusBase minusBase direction))).trans
          (norm_snd_le
            (globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration
                direction,
              (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                  configuration couplings.matterMassSquared realization direction,
                (globalMinimalPhysicalLLGraphLinearMap period hPeriod
                    configuration data analysis direction,
                  globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period
                    hPeriod configuration.physical plusBase minusBase direction)))))

/-- The true translated primitive matter input, including its nonzero base. -/
def regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (massSquared : Real)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod massSquared)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
  realization.toGraph configuration.physical.spinCMatter +
    globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
      massSquared realization direction

/-- The graph action at the translated matter input is C² in the joint norm. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMatterGraphAction_contDiff
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
    ContDiff Real 2
      (fun direction =>
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput
            period hPeriod configuration couplings.matterMassSquared realization
              direction)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hInput : ContDiff Real 2
      (fun direction : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical =>
        realization.toGraph configuration.physical.spinCMatter +
          globalMinimalPhysicalPairedMetricGaugeCoreMatterCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction) :=
    contDiff_const.add
      (globalMinimalPhysicalPairedMetricGaugeCoreMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff
  exact (programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
    couplings.matterMassSquared).comp hInput

set_option maxRecDepth 4000 in
/-- On the paired domain, the genuine matter block is the translated graph action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure).matter direction =
      programPPrimitiveSpinCMatterGraphAction period hPeriod
        couplings.matterMassSquared
        (regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput period
          hPeriod configuration couplings.matterMassSquared realization
            direction) := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration.physical couplings data plusBase minusBase
  let hZero :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change globalCandidateAMatterAction period hPeriod
      (family.datumAtTotal period hPeriod 0 hZero direction).1 couplings = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  change programPPrimitiveSpinCMatterSmoothAction period hPeriod
      couplings.matterMassSquared
        (configuration.physical.spinCMatter + direction.1.2) = _
  rw [← realization.action_agreement,
    realization.toGraph.map_add]
  rfl

/-- The genuine translated matter block is C² within the paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_contDiffWithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).matter
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact
    (regularGeneralMetricC2PairedMinimalPhysicalMatterGraphAction_contDiff
      period hPeriod configuration data analysis realization plusBase minusBase
        |>.contDiffWithinAt).congr_of_mem
      (fun direction hDirection =>
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_eq
          period hPeriod configuration data realization plusBase minusBase hBase
            measure direction hDirection)
      hPoint

/-- Gate marker: the eighth genuine block is C² with its base translation intact. -/
theorem regular_general_metric_c2_paired_minimal_physical_matter_c2_gate
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).matter
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
  regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_contDiffWithinAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
end JanusFormal
