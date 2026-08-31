import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertChartTransition4D

/-!
# Covered atlas descent on the reduced physical Hilbert space

Unlike a common-carrier family, this atlas only asks for transitions where two
member domains overlap.  A choice of one covering member then defines an
action and strong residual on the covered carrier; transition compatibility
proves that both are independent of that choice.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlas4D

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

/-- A reduced Hilbert atlas whose member domains cover an explicit carrier.
Transition data are required only on actual pairwise overlaps. -/
structure GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas
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
  cover : ∀ state ∈ carrier, ∃ index : Index,
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (chartData index) (reducedChart index)
          state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData index)).family.domain
  transition : ∀
      (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis), state ∈ carrier → (first second : Index) →
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (chartData first) (reducedChart first)
          state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData first)).family.domain →
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (chartData second) (reducedChart second)
          state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData second)).family.domain →
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
      (first second : Index)
      (hFirst : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
          hPeriod configuration data analysis (chartData first)
            (reducedChart first) state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData first)).family.domain)
      (hSecond : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
          hPeriod configuration data analysis (chartData second)
            (reducedChart second) state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData second)).family.domain),
    ((transition state hState first second hFirst hSecond).derivative.toContinuousLinearMap.comp
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis (chartData first)
            (reducedChart first))) =
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis (chartData second)
          (reducedChart second)

namespace GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (atlas : GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas
      period hPeriod (measure := measure) configuration data analysis)

/-- One reduced chart covers exactly the preimage of its admissible domain. -/
def singleton
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData) :
    GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas period
      hPeriod (measure := measure) configuration data analysis where
  Index := Unit
  chartData := fun _ ↦ chartData
  reducedChart := fun _ ↦ reducedChart
  carrier := {state |
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
      configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain}
  cover := by
    intro state hState
    exact ⟨(), hState⟩
  transition := by
    intro state hState first second hFirst hSecond
    cases first
    cases second
    exact GlobalCandidateALocalVariationalChartTransitionAt.refl period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData) _ hFirst
  derivative_compatible := by
    intro state hState first second hFirst hSecond
    cases first
    cases second
    apply ContinuousLinearMap.ext
    intro direction
    rfl

/-- A singleton chart with global admissible domain covers the full reduced
Hilbert space. -/
theorem singleton_carrier_eq_univ_of_domain_eq_univ
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)
    (hDomain :
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain = Set.univ) :
    (singleton period hPeriod chartData reducedChart).carrier = Set.univ := by
  ext state
  change globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
      configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain ↔
    state ∈ Set.univ
  rw [hDomain]
  simp only [Set.mem_univ, iff_self]

/-- A chosen covering member for a state of the covered carrier. -/
noncomputable def selectedIndex (state : atlas.carrier) : atlas.Index :=
  Classical.choose (atlas.cover state.1 state.2)

theorem selectedIndex_mem_domain (state : atlas.carrier) :
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (atlas.chartData (atlas.selectedIndex
          period hPeriod state))
        (atlas.reducedChart (atlas.selectedIndex period hPeriod state)) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData (atlas.selectedIndex
          period hPeriod state))).family.domain :=
  Classical.choose_spec (atlas.cover state.1 state.2)

/-- Action descended to the covered carrier. -/
noncomputable def action (state : atlas.carrier) : Real :=
  globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
    configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.reducedChart (atlas.selectedIndex period hPeriod state)) state.1

/-- Strong residual descended to the covered carrier. -/
noncomputable def residual (state : atlas.carrier) :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
      data analysis :=
  globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
    configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.reducedChart (atlas.selectedIndex period hPeriod state)) state.1

def IsEulerCritical (state : atlas.carrier) : Prop :=
  atlas.residual period hPeriod state = 0

theorem action_eq_chart (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain) :
    atlas.action period hPeriod state =
      globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
        configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 := by
  exact globalCandidateAMinimalPhysicalReducedHilbertAction_transition period
    hPeriod configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.chartData index)
      (atlas.reducedChart (atlas.selectedIndex period hPeriod state))
      (atlas.reducedChart index) state.1
      (atlas.transition state.1 state.2
        (atlas.selectedIndex period hPeriod state) index
          (atlas.selectedIndex_mem_domain period hPeriod state) hPoint)

theorem residual_eq_chart (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain) :
    atlas.residual period hPeriod state =
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
        configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 := by
  exact globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_transition
    period hPeriod configuration data analysis
      (atlas.chartData (atlas.selectedIndex period hPeriod state))
      (atlas.chartData index)
      (atlas.reducedChart (atlas.selectedIndex period hPeriod state))
      (atlas.reducedChart index) state.1
      (atlas.transition state.1 state.2
        (atlas.selectedIndex period hPeriod state) index
          (atlas.selectedIndex_mem_domain period hPeriod state) hPoint)
      (atlas.derivative_compatible state.1 state.2
        (atlas.selectedIndex period hPeriod state) index
          (atlas.selectedIndex_mem_domain period hPeriod state) hPoint)

/-- Criticality of the descended residual is Frechet stationarity in every
member that represents the covered state. -/
theorem isEulerCritical_iff_chart_fderiv
    (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain) :
    atlas.IsEulerCritical period hPeriod state ↔
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.reducedChart index)) state.1 = 0 := by
  rw [IsEulerCritical, atlas.residual_eq_chart period hPeriod state index hPoint]
  change GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
      hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state.1 ↔ _
  exact
    (globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_eq_zero_iff_residual
      period hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state.1 hPoint).symm

/-- The descended equation is the genuine local Euler equation in every
member that represents the state. -/
theorem isEulerCritical_iff_chart_localEuler
    (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain) :
    atlas.IsEulerCritical period hPeriod state ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (atlas.chartData index))
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.reducedChart index) state.1) = 0 := by
  rw [IsEulerCritical, atlas.residual_eq_chart period hPeriod state index hPoint]
  change GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
      hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state.1 ↔ _
  exact
    globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_localEuler
      period hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state.1

end GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlas4D
end JanusFormal
