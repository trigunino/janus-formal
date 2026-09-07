import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D

/-! # Same-action C² chart data at the actual paired origin

The paired family installs its own base geometry.  Its zero datum, rather
than an unrelated supplied geometry, is therefore the physical chart origin.
Reindexing by that datum preserves the original strong norm and action family.
The contract retains the C² socle of the earlier physical chart data without
requiring affine matter or nonlinear LL actions to be homogeneous quadratics.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongSameActionChartData4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- The minimal physical C² chart contract, with no quadratic-action fields. -/
structure ProgramPGlobalMinimalPhysicalSameActionChartData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  [normedAddCommGroup : NormedAddCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)]
  [normedSpace : NormedSpace Real
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)]
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  domain : Set
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  isOpen_domain : IsOpen domain
  zero_mem_domain :
    letI := normedAddCommGroup
    (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) ∈ domain
  datumAt : ∀ point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical, point ∈ domain →
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace
  datumAt_zero_configuration :
    letI := normedAddCommGroup
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  blocksC2Within : ∀ point (_hPoint : point ∈ domain),
    letI := normedAddCommGroup
    letI := normedSpace
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
        couplings NonNullFace NullFace :=
      { domain := domain, datumAt := datumAt }
    FullCoupledC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      domain point

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]

/-- The C² socle alone supplies an actual variational chart. -/
def ProgramPGlobalMinimalPhysicalSameActionChartData4D.toLocalVariationalChart
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalSameActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure := by
  letI := chartData.normedAddCommGroup
  letI := chartData.normedSpace
  have hZero :
      @Zero.zero _ chartData.normedAddCommGroup.toAddCommGroup.toZero =
        @Zero.zero _ (Submodule.addCommGroup
          (GlobalMinimalPhysicalFieldTangent period hPeriod
            configuration.physical)).toZero :=
    congrArg
      (fun group : AddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) => @Zero.zero _ group.toZero)
      chartData.toAddCommGroup_eq
  refine
    { Model := GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      normedAddCommGroup := chartData.normedAddCommGroup
      normedSpace := chartData.normedSpace
      family := { domain := chartData.domain, datumAt := chartData.datumAt }
      isOpen_domain := chartData.isOpen_domain
      zero_mem_domain := ?_
      blocksC2Within := ?_ }
  · change @Zero.zero _ chartData.normedAddCommGroup.toAddCommGroup.toZero ∈
      chartData.domain
    exact hZero.symm ▸ chartData.zero_mem_domain
  · intro point hPoint
    change point ∈ chartData.domain at hPoint
    convert chartData.blocksC2Within point hPoint using 1
    · congr 1
      congr
      exact congrArg
        (fun group : AddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical) => group.toZero)
        chartData.toAddCommGroup_eq

variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
    period hPeriod plusBase minusBase)

/-- The original family's exact zero datum determines both physical origin
and action data; no equality with the supplied geometry is assumed. -/
def pairedStrongSameActionOriginDatum :
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace :=
  (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
    period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
      0 (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration.physical plusBase minusBase hBase)

/-- Reindex the physical origin while retaining the nonminimal fields. -/
def pairedStrongSameActionOriginConfiguration :
    GlobalGaugeFixedFieldConfiguration period hPeriod where
  physical := (pairedStrongSameActionOriginDatum period hPeriod configuration
    data plusBase minusBase hBase).1
  nonminimal := configuration.nonminimal

def pairedStrongSameActionOriginData :
    GlobalCandidateAActionData period hPeriod
      (pairedStrongSameActionOriginConfiguration period hPeriod configuration
        data plusBase minusBase hBase).physical couplings NonNullFace NullFace :=
  (pairedStrongSameActionOriginDatum period hPeriod configuration data
    plusBase minusBase hBase).2

/-- The metric replacement does not alter the LL measure at zero. -/
theorem pairedStrongSameActionOriginConfiguration_llMeasure :
    (pairedStrongSameActionOriginConfiguration period hPeriod configuration
      data plusBase minusBase hBase).physical.coefficientFields.llMeasure =
        configuration.physical.coefficientFields.llMeasure := by
  change configuration.physical.coefficientFields.llMeasure + 0 = _
  exact add_zero _

/-- Positivity is transported through the unchanged zero LL measure. -/
def pairedStrongSameActionOriginAnalysis :
    GlobalAnalysisData period hPeriod
      (pairedStrongSameActionOriginConfiguration period hPeriod configuration
        data plusBase minusBase hBase).physical where
  llMeasure_pos point := by
    rw [pairedStrongSameActionOriginConfiguration_llMeasure]
    exact analysis.llMeasure_pos point

variable (measure : Measure (EffectiveQuotient period hPeriod))
  [IsFiniteMeasure measure]

/-- The existing affine-matter/nonlinear-LL family gives the C² datum at its
actual origin.  The original strong topology and family are retained verbatim. -/
def pairedStrongSameActionChartData :
    ProgramPGlobalMinimalPhysicalSameActionChartData4D period hPeriod
      (measure := measure)
      (pairedStrongSameActionOriginConfiguration period hPeriod configuration
        data plusBase minusBase hBase)
      (pairedStrongSameActionOriginData period hPeriod configuration data
        plusBase minusBase hBase)
      (pairedStrongSameActionOriginAnalysis period hPeriod configuration data
        analysis plusBase minusBase hBase) := by
  let chart := regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure
  exact
    { normedAddCommGroup := chart.normedAddCommGroup
      normedSpace := chart.normedSpace
      toAddCommGroup_eq := rfl
      toSMul_eq := rfl
      domain := chart.family.domain
      isOpen_domain := chart.isOpen_domain
      zero_mem_domain := chart.zero_mem_domain
      datumAt := chart.family.datumAt
      datumAt_zero_configuration := rfl
      blocksC2Within := chart.blocksC2Within }

/-- Packaging the new datum recovers exactly the established strong chart. -/
theorem pairedStrongSameActionChartData_toLocalVariationalChart :
    (pairedStrongSameActionChartData period hPeriod configuration data analysis
      realization plusBase minusBase hBase measure).toLocalVariationalChart
        period hPeriod _ _ _ =
      regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure :=
  rfl

/-- The datum pulls back the same covariant action at every admissible point. -/
theorem pairedStrongSameActionChartData_action_eq_CandidateA
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    globalCandidateALocalActionPullback period hPeriod
        ((pairedStrongSameActionChartData period hPeriod configuration data
          analysis realization plusBase minusBase hBase measure).toLocalVariationalChart
            period hPeriod _ _ _) point =
      globalCandidateACovariantAction period hPeriod
        ((regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
          period hPeriod configuration.physical couplings data plusBase
            minusBase).datumAt point hPoint).2 measure :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongLocalAction_eq_CandidateA
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

/-- Its Euler one-form is the established derivative of that same action. -/
theorem pairedStrongSameActionChartData_hasFDerivAt
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
        ((pairedStrongSameActionChartData period hPeriod configuration data
          analysis realization plusBase minusBase hBase measure).toLocalVariationalChart
            period hPeriod _ _ _))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongAction_hasFDerivAt period
    hPeriod configuration data analysis realization plusBase minusBase hBase
      measure point hPoint

include realization

/-- Gate 624: the actual paired family inhabits the same-action C² contract. -/
theorem paired_strong_same_action_chart_data_gate :
    Nonempty (ProgramPGlobalMinimalPhysicalSameActionChartData4D period hPeriod
      (measure := measure)
      (pairedStrongSameActionOriginConfiguration period hPeriod configuration
        data plusBase minusBase hBase)
      (pairedStrongSameActionOriginData period hPeriod configuration data
        plusBase minusBase hBase)
      (pairedStrongSameActionOriginAnalysis period hPeriod configuration data
        analysis plusBase minusBase hBase)) :=
  ⟨pairedStrongSameActionChartData period hPeriod configuration data analysis
    realization plusBase minusBase hBase measure⟩

end
end P0EFTJanusPairedStrongSameActionChartData4D
end JanusFormal
