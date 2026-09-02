import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransition4D

/-!
# Covered full-BRST atlas descent

Projection-compatible transitions are supplied only between chart members
which contain the same carrier state.  A covering member is then selected,
and the exact action, Euler covector and critical equation are proved
independent of that selection.  No canonical cross-chart transport is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTEulerOperatorRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransition4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

universe v

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section Atlas

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev FullChart (chartData :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev AtlasChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroupCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev AtlasChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpaceCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev AtlasChartModule
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  (AtlasChartNormedSpace period hPeriod configuration data analysis
    chartData).toModule

private abbrev AtlasChartAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  (AtlasChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toAddCommGroup

private abbrev AtlasChartTopologicalSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    TopologicalSpace
      (FullChart period hPeriod configuration data analysis chartData) :=
  (AtlasChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 11000) atlasChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  AtlasChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 11000) atlasChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  AtlasChartNormedSpace period hPeriod configuration data analysis chartData

/-- A covered carrier with full-BRST chart representatives and compatible
transitions on every pairwise overlap. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas where
  Index : Type v
  chartData : Index →
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis
  carrier : Set
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration)
  cover : ∀ state ∈ carrier, ∃ index : Index,
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis (chartData index) state ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (chartData index)
  transition : ∀
      (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period
        hPeriod configuration) (_hState : state ∈ carrier)
      (first second : Index),
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis (chartData first) state ∈
        globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis (chartData first) →
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis (chartData second) state ∈
        globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis (chartData second) →
    GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
      period hPeriod configuration data analysis (chartData first)
        (chartData second)
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis (chartData first) state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis (chartData second) state)

namespace GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas

variable
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (atlas :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas
        period hPeriod (measure := measure) configuration data analysis)

/-- The common full-BRST core realized in one atlas member. -/
def chartState
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration)
    (index : atlas.Index) :
    FullChart period hPeriod configuration data analysis
      (atlas.chartData index) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
    configuration data analysis (atlas.chartData index) state

/-- Every single full-BRST chart gives a covered atlas on the exact preimage
of its admissible domain. -/
def singleton
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas
      period hPeriod (measure := measure) configuration data analysis where
  Index := Unit
  chartData := fun _ ↦ chartData
  carrier := {state |
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis chartData state ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData}
  cover := by
    intro state hState
    exact ⟨(), hState⟩
  transition := by
    intro state hState first second hFirst hSecond
    cases first
    cases second
    exact
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt.refl
        period hPeriod chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period
            hPeriod configuration data analysis chartData state) hFirst

/-- Two arbitrary covering members give the same exact action. -/
theorem chart_action_eq_chart
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) (hState : state ∈ atlas.carrier)
    (first second : atlas.Index)
    (hFirst : atlas.chartState period hPeriod state first ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData first))
    (hSecond : atlas.chartState period hPeriod state second ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData second)) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis (atlas.chartData first)
          (atlas.chartState period hPeriod state first) =
      globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis (atlas.chartData second)
          (atlas.chartState period hPeriod state second) :=
  (atlas.transition state hState first second hFirst hSecond).action_eq
    period hPeriod

/-- Exact pullback covariance holds directly between any two covering
members. -/
theorem chart_eulerOperator_transition
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) (hState : state ∈ atlas.carrier)
    (first second : atlas.Index)
    (hFirst : atlas.chartState period hPeriod state first ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData first))
    (hSecond : atlas.chartState period hPeriod state second ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData second)) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData first)
          (atlas.chartState period hPeriod state first) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData second)
          (atlas.chartState period hPeriod state second)).comp
        (atlas.transition state hState first second hFirst
          hSecond).transport.toContinuousLinearMap :=
  (atlas.transition state hState first second hFirst
    hSecond).eulerOperator_transition period hPeriod

/-- The fixed-target residual equation is independent of two arbitrary
covering members. -/
theorem chart_residual_eq_zero_iff
    (state : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) (hState : state ∈ atlas.carrier)
    (first second : atlas.Index)
    (hFirst : atlas.chartState period hPeriod state first ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData first))
    (hSecond : atlas.chartState period hPeriod state second ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData second)) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis (atlas.chartData first)
            (atlas.chartState period hPeriod state first) = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis (atlas.chartData second)
            (atlas.chartState period hPeriod state second) = 0 :=
  (atlas.transition state hState first second hFirst hSecond).residual_eq_zero_iff
    period hPeriod

/-- A selected member covering a carrier state. -/
noncomputable def selectedIndex (state : atlas.carrier) : atlas.Index :=
  Classical.choose (atlas.cover state.1 state.2)

theorem selectedIndex_mem_domain (state : atlas.carrier) :
    atlas.chartState period hPeriod state.1
        (atlas.selectedIndex period hPeriod state) ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis
          (atlas.chartData (atlas.selectedIndex period hPeriod state)) :=
  Classical.choose_spec (atlas.cover state.1 state.2)

/-- The typed transition from the selected member to any other member
covering the same state. -/
noncomputable def selectedTransition (state : atlas.carrier)
    (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
      period hPeriod configuration data analysis
        (atlas.chartData (atlas.selectedIndex period hPeriod state))
        (atlas.chartData index)
        (atlas.chartState period hPeriod state.1
          (atlas.selectedIndex period hPeriod state))
        (atlas.chartState period hPeriod state.1 index) :=
  atlas.transition state.1 state.2
    (atlas.selectedIndex period hPeriod state) index
    (atlas.selectedIndex_mem_domain period hPeriod state) hIndex

/-- Exact action descended to the covered carrier. -/
noncomputable def action (state : atlas.carrier) : Real :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
    configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.chartState period hPeriod state.1
        (atlas.selectedIndex period hPeriod state))

/-- Euler covector in the selected local cotangent fibre. -/
noncomputable def eulerOperator (state : atlas.carrier) :
    FullChart period hPeriod configuration data analysis
        (atlas.chartData (atlas.selectedIndex period hPeriod state)) →L[Real]
      Real :=
  globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
    configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.chartState period hPeriod state.1
        (atlas.selectedIndex period hPeriod state))

/-- Fixed-target residual selected on the covered carrier.  Its zero locus,
rather than its coordinates, is the descended invariant. -/
noncomputable def residual (state : atlas.carrier) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D period
      hPeriod configuration data analysis :=
  globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
    period hPeriod configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.chartState period hPeriod state.1
        (atlas.selectedIndex period hPeriod state))

def IsEulerCritical (state : atlas.carrier) : Prop :=
  atlas.residual period hPeriod state = 0

theorem action_eq_chart (state : atlas.carrier) (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    atlas.action period hPeriod state =
      globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis (atlas.chartData index)
          (atlas.chartState period hPeriod state.1 index) :=
  (atlas.selectedTransition period hPeriod state index hIndex).action_eq
    period hPeriod

theorem eulerOperator_eq_chart_comp_transport
    (state : atlas.carrier) (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    atlas.eulerOperator period hPeriod state =
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData index)
          (atlas.chartState period hPeriod state.1 index)).comp
        (atlas.selectedTransition period hPeriod state index hIndex).transport.toContinuousLinearMap :=
  (atlas.selectedTransition period hPeriod state index hIndex).eulerOperator_transition
    period hPeriod

theorem residual_eq_zero_iff_chart
    (state : atlas.carrier) (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    atlas.residual period hPeriod state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
        period hPeriod configuration data analysis (atlas.chartData index)
          (atlas.chartState period hPeriod state.1 index) = 0 :=
  (atlas.selectedTransition period hPeriod state index hIndex).residual_eq_zero_iff
    period hPeriod

/-- Descended criticality is the exact local Euler equation in every member
covering the carrier state. -/
theorem isEulerCritical_iff_chart_eulerOperator_eq_zero
    (state : atlas.carrier) (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    atlas.IsEulerCritical period hPeriod state ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.chartState period hPeriod state.1 index) = 0 := by
  rw [IsEulerCritical, atlas.residual_eq_zero_iff_chart period hPeriod state
    index hIndex]
  simpa [GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt] using
    (global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate
      period hPeriod configuration data analysis (atlas.chartData index)
        (atlas.chartState period hPeriod state.1 index)).symm

/-- The descended critical locus is genuine Fréchet stationarity of the
full-BRST action in every covering member. -/
theorem isEulerCritical_iff_chart_fderiv_eq_zero
    (state : atlas.carrier) (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    atlas.IsEulerCritical period hPeriod state ↔
      @fderiv Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis
          (atlas.chartData index))
        (AtlasChartAddCommGroup period hPeriod configuration data analysis
          (atlas.chartData index))
        (AtlasChartModule period hPeriod configuration data analysis
          (atlas.chartData index))
        (AtlasChartTopologicalSpace period hPeriod configuration data analysis
          (atlas.chartData index))
        Real inferInstance inferInstance inferInstance
        (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
          configuration data analysis (atlas.chartData index))
        (atlas.chartState period hPeriod state.1 index) = 0 := by
  rw [IsEulerCritical, atlas.residual_eq_zero_iff_chart period hPeriod state
    index hIndex]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_fderiv_eq_zero
      period hPeriod (measure := measure) configuration data analysis
        (atlas.chartData index) (atlas.chartState period hPeriod state.1 index)
          hIndex

/-- Gate 272: a projection-compatible covered atlas carries an exact global
action, a transported Euler covector and a chart-independent critical locus. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_projection_compatible_covered_atlas_gate
    (state : atlas.carrier) (index : atlas.Index)
    (hIndex : atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)) :
    atlas.action period hPeriod state =
        globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.chartState period hPeriod state.1 index) ∧
      atlas.eulerOperator period hPeriod state =
        (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.chartState period hPeriod state.1 index)).comp
          (atlas.selectedTransition period hPeriod state index
            hIndex).transport.toContinuousLinearMap ∧
      (atlas.IsEulerCritical period hPeriod state ↔
        globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.chartState period hPeriod state.1 index) = 0) :=
  ⟨atlas.action_eq_chart period hPeriod state index hIndex,
    atlas.eulerOperator_eq_chart_comp_transport period hPeriod state index hIndex,
    atlas.isEulerCritical_iff_chart_eulerOperator_eq_zero period hPeriod state
      index hIndex⟩

end GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas
end Atlas
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas4D
end JanusFormal
