import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartCovariance4D

/-!
# Projection-compatible full-BRST chart transitions

The data used by Gate 270 are packaged as one typed transition. Identity and
composition are constructed, and composition preserves exact action, Euler
covector and critical-locus covariance. No cross-chart transition is invented.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransition4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartCovariance4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

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

section Transition

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev MinimalChart (chartData :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev FullChart (chartData :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev TransitionChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroupCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev TransitionChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpaceCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) transitionChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  TransitionChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 11000) transitionChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  TransitionChartNormedSpace period hPeriod configuration data analysis chartData

/-- A full-BRST overlap transition whose bounded transport intertwines all
three projections used by the exact Euler covector. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
    (firstChartData secondChartData :
      ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
        (measure := measure) configuration data analysis)
    (firstState :
      FullChart period hPeriod configuration data analysis firstChartData)
    (secondState :
      FullChart period hPeriod configuration data analysis secondChartData) where
  physicalTransition :
    GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (MinimalChart period hPeriod configuration data analysis firstChartData)
      (MinimalChart period hPeriod configuration data analysis secondChartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
        hPeriod configuration data analysis firstChartData firstState)
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
        hPeriod configuration data analysis secondChartData secondState)
  transport :
    FullChart period hPeriod configuration data analysis firstChartData ≃L[Real]
      FullChart period hPeriod configuration data analysis secondChartData
  diffeomorphismGraphState :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
        period hPeriod configuration data analysis firstChartData firstState =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
        period hPeriod configuration data analysis secondChartData secondState
  abelianState :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
        configuration data analysis firstChartData firstState =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
        configuration data analysis secondChartData secondState
  physicalTransport :
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
        configuration data analysis secondChartData).comp
        transport.toContinuousLinearMap =
      physicalTransition.derivative.toContinuousLinearMap.comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis firstChartData)
  diffeomorphismGraphTransport :
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
        period hPeriod configuration data analysis secondChartData).comp
        transport.toContinuousLinearMap =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
        period hPeriod configuration data analysis firstChartData
  abelianTransport :
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
        configuration data analysis secondChartData).comp
        transport.toContinuousLinearMap =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
        configuration data analysis firstChartData

namespace GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt

variable
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {firstChartData secondChartData thirdChartData :
      ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
        (measure := measure) configuration data analysis}
    {firstState :
      FullChart period hPeriod configuration data analysis firstChartData}
    {secondState :
      FullChart period hPeriod configuration data analysis secondChartData}
    {thirdState :
      FullChart period hPeriod configuration data analysis thirdChartData}

/-- Identity projection-compatible transition at every admissible state. -/
def refl
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hState : state ∈ globalCandidateAGaugeFixedNonlinearFullBRSTDomain period
      hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
      period hPeriod configuration data analysis chartData chartData state state := by
  have hPhysical :
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
          configuration data analysis chartData state ∈
        (MinimalChart period hPeriod configuration data analysis chartData).family.domain := by
    change globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
        hPeriod configuration data analysis chartData state ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain at hState
    exact hState
  let physicalTransition :=
    GlobalCandidateALocalVariationalChartTransitionAt.refl period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
        configuration data analysis chartData state) hPhysical
  refine
    { physicalTransition := physicalTransition
      transport := ContinuousLinearEquiv.refl Real
        (FullChart period hPeriod configuration data analysis chartData)
      diffeomorphismGraphState := rfl
      abelianState := rfl
      physicalTransport := ?_
      diffeomorphismGraphTransport := ?_
      abelianTransport := ?_ }
  all_goals
    apply ContinuousLinearMap.ext
    intro direction
    rfl

/-- Projection-compatible transitions compose. -/
def trans
    (firstSecond :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis firstChartData secondChartData
          firstState secondState)
    (secondThird :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis secondChartData thirdChartData
          secondState thirdState) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
      period hPeriod configuration data analysis firstChartData thirdChartData
        firstState thirdState := by
  let physicalTransition :=
    GlobalCandidateALocalVariationalChartTransitionAt.trans period hPeriod
      firstSecond.physicalTransition secondThird.physicalTransition
  let transport := firstSecond.transport.trans secondThird.transport
  refine
    { physicalTransition := physicalTransition
      transport := transport
      diffeomorphismGraphState :=
        firstSecond.diffeomorphismGraphState.trans
          secondThird.diffeomorphismGraphState
      abelianState := firstSecond.abelianState.trans secondThird.abelianState
      physicalTransport := ?_
      diffeomorphismGraphTransport := ?_
      abelianTransport := ?_ }
  · apply ContinuousLinearMap.ext
    intro direction
    have hSecondThird := congrArg
      (fun linearMap => linearMap (firstSecond.transport direction))
      secondThird.physicalTransport
    have hFirstSecond := congrArg (fun linearMap => linearMap direction)
      firstSecond.physicalTransport
    simp only [ContinuousLinearMap.comp_apply] at hSecondThird hFirstSecond
    change
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
          configuration data analysis thirdChartData
          (secondThird.transport (firstSecond.transport direction)) =
        secondThird.physicalTransition.derivative
          (firstSecond.physicalTransition.derivative
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
              hPeriod configuration data analysis firstChartData direction))
    exact hSecondThird.trans
      (congrArg secondThird.physicalTransition.derivative hFirstSecond)
  · apply ContinuousLinearMap.ext
    intro direction
    have hSecondThird := congrArg
      (fun linearMap => linearMap (firstSecond.transport direction))
      secondThird.diffeomorphismGraphTransport
    have hFirstSecond := congrArg (fun linearMap => linearMap direction)
      firstSecond.diffeomorphismGraphTransport
    simp only [ContinuousLinearMap.comp_apply] at hSecondThird hFirstSecond
    change
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis thirdChartData
          (secondThird.transport (firstSecond.transport direction)) =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData direction
    exact hSecondThird.trans hFirstSecond
  · apply ContinuousLinearMap.ext
    intro direction
    have hSecondThird := congrArg
      (fun linearMap => linearMap (firstSecond.transport direction))
      secondThird.abelianTransport
    have hFirstSecond := congrArg (fun linearMap => linearMap direction)
      firstSecond.abelianTransport
    simp only [ContinuousLinearMap.comp_apply] at hSecondThird hFirstSecond
    change
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis thirdChartData
          (secondThird.transport (firstSecond.transport direction)) =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData direction
    exact hSecondThird.trans hFirstSecond

/-- Both endpoints of a typed transition lie in their full-BRST domains. -/
theorem states_mem_domain
    (transition :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis firstChartData secondChartData
          firstState secondState) :
    firstState ∈ globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis firstChartData ∧
      secondState ∈ globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis secondChartData := by
  constructor
  · change globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
        hPeriod configuration data analysis firstChartData firstState ∈
      (MinimalChart period hPeriod configuration data analysis firstChartData).family.domain
    exact transition.physicalTransition.first_mem_domain
  · change globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
        hPeriod configuration data analysis secondChartData secondState ∈
      (MinimalChart period hPeriod configuration data analysis secondChartData).family.domain
    exact transition.physicalTransition.second_mem_domain

/-- Exact action covariance carried by a typed compatible transition. -/
theorem action_eq
    (transition :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis firstChartData secondChartData
          firstState secondState) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
        data analysis firstChartData firstState =
      globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
        data analysis secondChartData secondState :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAction_eq_of_projection_compatible
    period hPeriod configuration data analysis firstChartData secondChartData
    firstState secondState transition.physicalTransition
    transition.diffeomorphismGraphState transition.abelianState

/-- Exact Euler-covector covariance carried by a typed compatible transition. -/
theorem eulerOperator_transition
    (transition :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis firstChartData secondChartData
          firstState secondState) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis firstChartData firstState =
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis secondChartData secondState).comp
          transition.transport.toContinuousLinearMap :=
  globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_transition_of_projection_compatible
    period hPeriod configuration data analysis firstChartData secondChartData
    firstState secondState transition.physicalTransition transition.transport
    transition.diffeomorphismGraphState transition.abelianState
    transition.physicalTransport transition.diffeomorphismGraphTransport
    transition.abelianTransport

/-- The fixed-ambient critical equation descends along a typed transition. -/
theorem residual_eq_zero_iff
    (transition :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis firstChartData secondChartData
          firstState secondState) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis firstChartData firstState = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis secondChartData secondState = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_projection_compatible
    period hPeriod configuration data analysis firstChartData secondChartData
    firstState secondState transition.physicalTransition transition.transport
    transition.diffeomorphismGraphState transition.abelianState
    transition.physicalTransport transition.diffeomorphismGraphTransport
    transition.abelianTransport

/-- Gate 271: compatible full-BRST transitions contain identities, compose,
and every composite preserves the exact action, Euler covector and critical
equation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_projection_compatible_chart_transition_gate
    (firstSecond :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis firstChartData secondChartData
          firstState secondState)
    (secondThird :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
        period hPeriod configuration data analysis secondChartData thirdChartData
          secondState thirdState) :
    let firstThird := firstSecond.trans period hPeriod secondThird
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
          data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
          data analysis thirdChartData thirdState ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis firstChartData firstState =
        (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis thirdChartData thirdState).comp
            firstThird.transport.toContinuousLinearMap ∧
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
            period hPeriod configuration data analysis firstChartData firstState = 0 ↔
        globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
            period hPeriod configuration data analysis thirdChartData thirdState = 0) := by
  dsimp only
  let firstThird := firstSecond.trans period hPeriod secondThird
  exact ⟨firstThird.action_eq period hPeriod,
    firstThird.eulerOperator_transition period hPeriod,
    firstThird.residual_eq_zero_iff period hPeriod⟩

end GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransitionAt
end Transition
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartTransition4D
end JanusFormal
