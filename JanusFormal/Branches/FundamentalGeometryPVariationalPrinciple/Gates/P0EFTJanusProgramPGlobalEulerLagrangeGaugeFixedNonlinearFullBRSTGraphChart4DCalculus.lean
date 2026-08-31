import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D

/-!
# Calculus for the nonlinear physical chart with the full BRST graph

This continuation isolates the exact first variation and local C² regularity so
Lean can elaborate the full relational chart with bounded memory.
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
local instance (priority := 11000) alignedRealNontriviallyNormedFieldCalculus :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

private theorem continuousLinearMap_comp_contDiffAt_two
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (projection : E →L[Real] F) (action : F → Real) (state : E)
    (hAction : ContDiffAt Real 2 action (projection state)) :
    ContDiffAt Real 2 (fun point => action (projection point)) state :=
  hAction.comp state projection.contDiff.contDiffAt

private theorem contDiffAt_add_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (first second : E → Real) (state : E)
    (hFirst : ContDiffAt Real 2 first state)
    (hSecond : ContDiffAt Real 2 second state) :
    ContDiffAt Real 2 (fun point => first point + second point) state :=
  hFirst.add hSecond

private theorem continuousLinearMap_add_comp_hasFDerivAt
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (first : E →L[Real] F) (second : E →L[Real] G)
    (firstAction : F → Real) (secondAction : G → Real)
    (firstDerivative : F →L[Real] Real)
    (secondDerivative : G →L[Real] Real)
    (state : E)
    (hFirst : HasFDerivAt firstAction firstDerivative (first state))
    (hSecond : HasFDerivAt secondAction secondDerivative (second state)) :
    HasFDerivAt
      (fun point => firstAction (first point) + secondAction (second point))
      (firstDerivative.comp first + secondDerivative.comp second) state :=
  (hFirst.comp state first.hasFDerivAt).add
    (hSecond.comp state second.hasFDerivAt)

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceCalculus :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldCalculus :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceCalculus :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceCalculus :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteCalculus :
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
local instance (priority := 10001) fullDiffeomorphismChartNormedAddCommGroupCalculus :
    NormedAddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedAddCommGroup
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedSpaceCalculus :
    NormedSpace Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedSpace
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartAddCommGroupCalculus :
    AddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupCalculus period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartTopologicalSpaceCalculus :
    TopologicalSpace
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupCalculus period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartModuleCalculus :
    Module Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedSpaceCalculus period hPeriod configuration data
    analysis chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedAddCommGroupCalculus :
    NormedAddCommGroup
      (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedSpaceCalculus :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphAddCommGroupCalculus :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupCalculus period hPeriod configuration
    data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphTopologicalSpaceCalculus :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupCalculus period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphModuleCalculus :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedSpaceCalculus period hPeriod configuration data).toModule

local instance (priority := 10002) nonlinearFullAmbientModuleCalculus :
    Module Real
      (FullAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedAddCommGroupCalculus :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (FullAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (nonlinearFullAmbientModuleCalculus period hPeriod (measure := measure)
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedSpaceCalculus :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  Submodule.normedSpace
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartModuleCalculus :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartAddCommGroupCalculus :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartTopologicalSpaceCalculus :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
/-- Exact nonlinear physical action plus both off-shell BRST gauge-fixing
actions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAction
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
      hPeriod configuration data analysis chartData) : Real :=
  globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period hPeriod
      configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
        period hPeriod configuration data analysis chartData state) +
    globalPairedAbelianOffShellGraphAction period hPeriod
      (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
        hPeriod configuration data analysis chartData state)

/-- Exact first variation on the nonlinear full-BRST chart. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
      hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData →L[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTEulerOperator period
      hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
        period hPeriod configuration data analysis chartData state)).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData) +
  (globalPairedAbelianOffShellHessian period hPeriod
      (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
        hPeriod configuration data analysis chartData state)).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
      hPeriod configuration data analysis chartData)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_hasFDerivAt
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
      hPeriod configuration data analysis chartData)
    (hState : state ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) :
    @HasFDerivAt Real alignedRealNontriviallyNormedFieldCalculus
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData)
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData).toAddCommGroup
      (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
        configuration data analysis chartData).toModule
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      Real
      (inferInstance : NormedAddCommGroup Real).toAddCommGroup
      (inferInstance : NormedSpace Real Real).toModule
      (inferInstance : NormedAddCommGroup Real).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis chartData state) state := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAction
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
        hPeriod configuration data analysis chartData state ∈
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData at hState
  exact
    @continuousLinearMap_add_comp_hasFDerivAt
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData)
      (DiffeomorphismChart period hPeriod configuration data analysis chartData)
      (AbelianGraph period hPeriod configuration data)
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData)
      (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
        configuration data analysis chartData)
      (fullDiffeomorphismChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData)
      (fullDiffeomorphismChartNormedSpaceCalculus period hPeriod configuration data
        analysis chartData)
      (fullAbelianGraphNormedAddCommGroupCalculus period hPeriod configuration data)
      (fullAbelianGraphNormedSpaceCalculus period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
        hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period
        hPeriod configuration data analysis chartData)
      (globalPairedAbelianOffShellGraphAction period hPeriod
        (BaseMetric period hPeriod configuration data))
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTEulerOperator period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
          period hPeriod configuration data analysis chartData state))
      (globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state))
      state
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_hasFDerivAt
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
          period hPeriod configuration data analysis chartData state) hState)
      (globalPairedAbelianOffShellGraphAction_hasFDerivAt period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state))
private theorem nonlinearFullBRSTDiffeomorphismAction_contDiffAt_two
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
      hPeriod configuration data analysis chartData)
    (hState :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
          hPeriod configuration data analysis chartData state ∈
        globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period
          hPeriod configuration data analysis chartData) :
    @ContDiffAt Real alignedRealNontriviallyNormedFieldCalculus
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData)
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData)
      (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance 2
      (fun point =>
        globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
            period hPeriod configuration data analysis chartData point))
      state :=
  @continuousLinearMap_comp_contDiffAt_two
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
      configuration data analysis chartData)
    (DiffeomorphismChart period hPeriod configuration data analysis chartData)
    (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration data
      analysis chartData)
    (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
      configuration data analysis chartData)
    (fullDiffeomorphismChartNormedAddCommGroupCalculus period hPeriod configuration
      data analysis chartData)
    (fullDiffeomorphismChartNormedSpaceCalculus period hPeriod configuration data
      analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period hPeriod
      configuration data analysis chartData)
    state
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_contDiffAt_two
      period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
        hPeriod configuration data analysis chartData state) hState)

private theorem nonlinearFullBRSTAbelianAction_contDiffAt_two
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
      hPeriod configuration data analysis chartData) :
    @ContDiffAt Real alignedRealNontriviallyNormedFieldCalculus
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData)
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData)
      (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance 2
      (fun point =>
        globalPairedAbelianOffShellGraphAction period hPeriod
          (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
            hPeriod configuration data analysis chartData point))
      state :=
  @continuousLinearMap_comp_contDiffAt_two
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
      configuration data analysis chartData)
    (AbelianGraph period hPeriod configuration data)
    (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration data
      analysis chartData)
    (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
      configuration data analysis chartData)
    (fullAbelianGraphNormedAddCommGroupCalculus period hPeriod configuration data)
    (fullAbelianGraphNormedSpaceCalculus period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
      configuration data analysis chartData)
    (globalPairedAbelianOffShellGraphAction period hPeriod
      (BaseMetric period hPeriod configuration data))
    state
    (@ContDiff.contDiffAt Real alignedRealNontriviallyNormedFieldCalculus
      (AbelianGraph period hPeriod configuration data)
      (fullAbelianGraphNormedAddCommGroupCalculus period hPeriod configuration data)
      (fullAbelianGraphNormedSpaceCalculus period hPeriod configuration data)
      Real inferInstance inferInstance
      (globalPairedAbelianOffShellGraphAction period hPeriod
        (BaseMetric period hPeriod configuration data))
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
        hPeriod configuration data analysis chartData state)
      2
      (globalPairedAbelianOffShellGraphAction_contDiff_two period hPeriod
        (BaseMetric period hPeriod configuration data)))

set_option maxHeartbeats 400000 in
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_contDiffAt_two
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period
      hPeriod configuration data analysis chartData)
    (hState : state ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) :
    @ContDiffAt Real alignedRealNontriviallyNormedFieldCalculus
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData)
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod configuration
        data analysis chartData)
      (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance 2
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData) state := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAction
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
        hPeriod configuration data analysis chartData state ∈
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData at hState
  have hDiffeomorphism :=
    nonlinearFullBRSTDiffeomorphismAction_contDiffAt_two period hPeriod
      configuration data analysis chartData state hState
  have hAbelian :=
    nonlinearFullBRSTAbelianAction_contDiffAt_two period hPeriod
      configuration data analysis chartData state
  exact
    @contDiffAt_add_two
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData)
      (nonlinearFullBRSTChartNormedAddCommGroupCalculus period hPeriod
        (measure := measure) configuration data analysis chartData)
      (nonlinearFullBRSTChartNormedSpaceCalculus period hPeriod
        (measure := measure) configuration data analysis chartData)
      _ _ state hDiffeomorphism hAbelian
end FullBRSTChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
end JanusFormal
