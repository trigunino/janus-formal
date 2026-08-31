import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertChartTransition4D

/-!
# Atlas descent of the reduced nonlinear Hilbert Euler residual

A compatible family of reduced Hilbert charts defines one action and one
strong Euler residual on their common carrier, independently of the selected
chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertAtlasResidual4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertChartTransition4D

universe v

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Exact compatibility needed to descend the nonlinear residual through a
family of reduced Hilbert charts. -/
structure GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  Index : Type v
  chartData : Index → ProgramPGlobalMinimalPhysicalActionChartData4D period
    hPeriod (measure := measure) configuration data analysis
  reducedChart : (index : Index) →
    ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period hPeriod
      configuration data analysis (chartData index)
  carrier : Set (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
    configuration data analysis)
  referenceIndex : Index
  transition : ∀ (state : GlobalCandidateAMinimalPhysicalReducedHilbert period
      hPeriod configuration data analysis), state ∈ carrier →
    ∀ first second : Index,
      GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData first))
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData second))
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis (chartData first) (reducedChart first)
            state)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis (chartData second) (reducedChart second)
            state)
  derivative_compatible : ∀
      (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis) (hState : state ∈ carrier)
      (first second : Index),
    ((transition state hState first second).derivative.toContinuousLinearMap.comp
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis (chartData first)
          (reducedChart first))) =
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis (chartData second)
          (reducedChart second)

namespace GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (atlas :
      GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas
        period hPeriod (measure := measure) configuration data analysis)

/-- One reduced chart gives a singleton residual atlas on its admissible
preimage. -/
def singleton
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData) :
    GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas period
      hPeriod (measure := measure) configuration data analysis where
  Index := Unit
  chartData := fun _ ↦ chartData
  reducedChart := fun _ ↦ reducedChart
  carrier := {state |
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
      configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain}
  referenceIndex := ()
  transition := by
    intro state hState first second
    cases first
    cases second
    exact GlobalCandidateALocalVariationalChartTransitionAt.refl period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData) _ hState
  derivative_compatible := by
    intro state hState first second
    cases first
    cases second
    apply ContinuousLinearMap.ext
    intro direction
    rfl

/-- Chart-independent action, defined in the reference chart. -/
def action :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
    configuration data analysis (atlas.chartData atlas.referenceIndex)
      (atlas.reducedChart atlas.referenceIndex)

/-- Chart-independent strong Euler residual. -/
noncomputable def residual :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis →
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
    configuration data analysis (atlas.chartData atlas.referenceIndex)
      (atlas.reducedChart atlas.referenceIndex)

/-- The descended reduced Euler equation. -/
def IsEulerCritical
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) : Prop :=
  atlas.residual period hPeriod state = 0

theorem action_eq_chart
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index) :
    atlas.action period hPeriod state =
      globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
        configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state := by
  exact globalCandidateAMinimalPhysicalReducedHilbertAction_transition period
    hPeriod configuration data analysis (atlas.chartData atlas.referenceIndex)
      (atlas.chartData index) (atlas.reducedChart atlas.referenceIndex)
      (atlas.reducedChart index) state
      (atlas.transition state hState atlas.referenceIndex index)

theorem residual_eq_chart
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index) :
    atlas.residual period hPeriod state =
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
        configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state := by
  exact globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_transition
    period hPeriod configuration data analysis
      (atlas.chartData atlas.referenceIndex) (atlas.chartData index)
      (atlas.reducedChart atlas.referenceIndex) (atlas.reducedChart index) state
      (atlas.transition state hState atlas.referenceIndex index)
      (atlas.derivative_compatible state hState atlas.referenceIndex index)

/-- The descended equation is Frechet stationarity in every atlas chart. -/
theorem isEulerCritical_iff_chart_fderiv
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index) :
    atlas.IsEulerCritical period hPeriod state ↔
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.reducedChart index)) state = 0 := by
  rw [IsEulerCritical, atlas.residual_eq_chart period hPeriod state hState index]
  change GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
      hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state ↔ _
  exact
    (globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_eq_zero_iff_residual
      period hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state
        (atlas.transition state hState atlas.referenceIndex index).second_mem_domain).symm

end GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertAtlasResidual4D
end JanusFormal
