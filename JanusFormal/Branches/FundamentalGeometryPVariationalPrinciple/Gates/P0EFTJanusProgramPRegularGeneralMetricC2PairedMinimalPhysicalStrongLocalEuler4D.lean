import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalFullActionC24D

/-! # Strong local Candidate-A chart and Euler operator -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D

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
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalFullActionC24D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- The exact paired domain is open also in the stronger LL graph topology. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
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
    IsOpen
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [← regularGeneralMetricC2PairedMinimalPhysicalOpenAdmissibleDomain_eq
    period hPeriod configuration.physical plusBase minusBase]
  change IsOpen
    ((globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase) ⁻¹'
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase
        minusBase)
  exact (regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
    plusBase minusBase).preimage
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase).continuous

/-- Concrete local Candidate-A chart carrying the strong LL graph topology. -/
noncomputable def regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
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
    [IsFiniteMeasure measure] :
    GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  refine
    { Model := GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical
      normedAddCommGroup :=
        globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period
          hPeriod configuration data analysis realization plusBase minusBase
            (canonicalDivergenceFreeLLFrame period hPeriod)
      normedSpace :=
        globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
          configuration data analysis realization plusBase minusBase
            (canonicalDivergenceFreeLLFrame period hPeriod)
      family :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
          period hPeriod configuration.physical couplings data plusBase minusBase
      isOpen_domain :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
          period hPeriod configuration data analysis realization plusBase
            minusBase
      zero_mem_domain :=
        zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
          period hPeriod configuration.physical plusBase minusBase hBase
      blocksC2Within := ?_ }
  intro point hPoint
  change FullCoupledC2WithinAt
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure)
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
      configuration.physical plusBase minusBase) point
  exact regularGeneralMetricC2PairedMinimalPhysicalNineBlockC2WithinAt period
    hPeriod configuration data analysis realization plusBase minusBase hBase
      measure point hPoint

/-- The exact strong-chart Euler one-form of Candidate A. -/
noncomputable def regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
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
    [IsFiniteMeasure measure] :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
        →L[Real] Real := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact globalCandidateALocalEulerLagrangeOperator period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure)

/-- On every admissible direction, the strong pullback is the genuine action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLocalAction_eq_CandidateA
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
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    globalCandidateALocalActionPullback period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure) direction =
      globalCandidateACovariantAction period hPeriod
        ((regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
          period hPeriod configuration.physical couplings data plusBase
            minusBase).datumAt direction hDirection).2 measure := by
  exact globalCandidateALocalActionPullback_eq_covariant_of_mem period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure) direction hDirection

/-- The displayed Euler one-form is the derivative of that same action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongAction_hasFDerivAt
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
    HasFDerivAt
      (globalCandidateALocalActionPullback period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact globalCandidateALocalAction_hasFDerivAt period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure) point hPoint

/-- The strong Euler operator is differentiable on the physical domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_differentiableAt
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
    DifferentiableAt Real
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact globalCandidateALocalEulerLagrangeOperator_differentiableAt period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure) point hPoint

/-- Gate marker: a concrete strong local Euler operator is derived. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_local_euler_gate
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
    HasFDerivAt
        (globalCandidateALocalActionPullback period hPeriod
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase measure))
        (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point) point ∧
      DifferentiableAt Real
        (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure) point :=
  ⟨regularGeneralMetricC2PairedMinimalPhysicalStrongAction_hasFDerivAt period
      hPeriod configuration data analysis realization plusBase minusBase hBase
        measure point hPoint,
    regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_differentiableAt period
      hPeriod configuration data analysis realization plusBase minusBase hBase
        measure point hPoint⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
end JanusFormal
