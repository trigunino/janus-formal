import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4DReduction

/-!
# Terminal support theorem for nonlinear full-BRST Gate 223

This final continuation packages openness, the zero state, and the exact core bijection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 8000000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldTerminal :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩


variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceTerminal :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldTerminal :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceTerminal :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceTerminal :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteTerminal :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section FullBRSTChart

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev DiffeomorphismChart :=
  GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D period
    hPeriod configuration data analysis chartData

private abbrev AbelianGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev FullAmbient :=
  DiffeomorphismChart period hPeriod configuration data analysis chartData ×
    AbelianGraph period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedAddCommGroupTerminal :
    NormedAddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedAddCommGroup
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedSpaceTerminal :
    NormedSpace Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedSpace
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartAddCommGroupTerminal :
    AddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupTerminal period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartTopologicalSpaceTerminal :
    TopologicalSpace
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupTerminal period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartModuleTerminal :
    Module Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedSpaceTerminal period hPeriod configuration data
    analysis chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedAddCommGroupTerminal :
    NormedAddCommGroup
      (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedSpaceTerminal :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphAddCommGroupTerminal :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupTerminal period hPeriod configuration
    data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphTopologicalSpaceTerminal :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupTerminal period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphModuleTerminal :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedSpaceTerminal period hPeriod configuration data).toModule

local instance (priority := 10002) nonlinearFullAmbientModuleTerminal :
    Module Real
      (FullAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedAddCommGroupTerminal :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (FullAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (nonlinearFullAmbientModuleTerminal period hPeriod (measure := measure)
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedSpaceTerminal :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  Submodule.normedSpace
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartModuleTerminal :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedSpaceTerminal period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartAddCommGroupTerminal :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupTerminal period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartTopologicalSpaceTerminal :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupTerminal period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
/-- Gate 223: the exact nonlinear physical chart and both completed BRST
graphs form one faithful relational chart with a unique Abelian potential. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_graph_chart_gate :
    IsOpen
        (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis chartData) ∧
      (0 : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
        hPeriod configuration data analysis chartData) ∈
          globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
            configuration data analysis chartData ∧
      Function.Bijective
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData) := by
  exact ⟨globalCandidateAGaugeFixedNonlinearFullBRSTDomain_isOpen period hPeriod
      configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTDomain_zero_mem period hPeriod
      configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_injective period
      hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_surjective period
      hPeriod configuration data analysis chartData⟩
end FullBRSTChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
end JanusFormal
