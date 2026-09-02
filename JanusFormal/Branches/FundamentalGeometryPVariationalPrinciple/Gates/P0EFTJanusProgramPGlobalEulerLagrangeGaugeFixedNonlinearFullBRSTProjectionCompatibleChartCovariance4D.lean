import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTEulerOperatorRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D

/-!
# Projection-compatible full-BRST chart covariance

The full-BRST action, Euler covector and fixed-ambient critical equation are
transported between two charts whenever a bounded linear chart transport is
supplied and intertwines the physical, diffeomorphism-graph and Abelian
projections.  No canonical transport or atlas is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartCovariance4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Filter
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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

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

section Covariance

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

private abbrev DiffeomorphismGraph :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev AbelianGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev CovarianceChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroupCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev CovarianceChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpaceCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) covarianceChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  CovarianceChartNormedAddCommGroup period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) covarianceChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  CovarianceChartNormedSpace period hPeriod configuration data analysis chartData

/-- The physical projection seen directly from the full-BRST chart. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      (MinimalChart period hPeriod configuration data analysis chartData).Model :=
  (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
      period hPeriod configuration data analysis chartData).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData)

/-- The diffeomorphism BRST graph projection seen from the full-BRST chart. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      DiffeomorphismGraph period hPeriod configuration data :=
  (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection period
      hPeriod configuration data analysis chartData).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData)

/-- Exact three-factor expansion of the full-BRST action. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_apply
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
        data analysis chartData state =
      (globalCandidateALocalActionPullback period hPeriod
          (MinimalChart period hPeriod configuration data analysis chartData))
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis chartData state) +
        globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
          couplings (globalCandidateAMetricBySector period hPeriod data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
            period hPeriod configuration data analysis chartData state) +
      globalPairedAbelianOffShellGraphAction period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state) :=
  rfl

/-- Exact three-factor expansion of the full-BRST Euler covector. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_apply
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (state direction : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis chartData state direction =
      (globalCandidateALocalEulerLagrangeOperator period hPeriod
          (MinimalChart period hPeriod configuration data analysis chartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis chartData state))
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis chartData direction) +
        (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
          couplings (globalCandidateAMetricBySector period hPeriod data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
            period hPeriod configuration data analysis chartData state))
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
            period hPeriod configuration data analysis chartData direction) +
      (globalPairedAbelianOffShellHessian period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
            hPeriod configuration data analysis chartData state))
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData direction) :=
  rfl

variable
    (firstChartData secondChartData :
      ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
        (measure := measure) configuration data analysis)
    (firstState :
      FullChart period hPeriod configuration data analysis firstChartData)
    (secondState :
      FullChart period hPeriod configuration data analysis secondChartData)

/-- Equality of the exact full-BRST actions under compatible projected states. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_eq_of_projection_compatible
    (physicalTransition :
      GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis firstChartData)
        (MinimalChart period hPeriod configuration data analysis secondChartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis firstChartData firstState)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis secondChartData secondState))
    (hDiffeomorphismGraphState :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData secondState)
    (hAbelianState :
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData secondState) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
        data analysis firstChartData firstState =
      globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
        data analysis secondChartData secondState := by
  have hPhysicalAction := physicalTransition.action_eventuallyEq.self_of_nhds
  simp only [Function.comp_apply, physicalTransition.maps_point] at hPhysicalAction
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAction_apply,
    globalCandidateAGaugeFixedNonlinearFullBRSTAction_apply]
  rw [hDiffeomorphismGraphState, hAbelianState, hPhysicalAction]

/-- Exact full-BRST Euler covariance under a bounded transport intertwining all
three factor projections. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_transition_of_projection_compatible
    (physicalTransition :
      GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis firstChartData)
        (MinimalChart period hPeriod configuration data analysis secondChartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis firstChartData firstState)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis secondChartData secondState))
    (transport :
      FullChart period hPeriod configuration data analysis firstChartData ≃L[Real]
        FullChart period hPeriod configuration data analysis secondChartData)
    (hDiffeomorphismGraphState :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData secondState)
    (hAbelianState :
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData secondState)
    (hPhysicalTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        physicalTransition.derivative.toContinuousLinearMap.comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis firstChartData))
    (hDiffeomorphismGraphTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData)
    (hAbelianTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis firstChartData firstState =
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis secondChartData secondState).comp
          transport.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro direction
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis firstChartData firstState direction =
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis secondChartData secondState
          (transport direction)
  have hPhysicalDirection :=
    congrArg (fun linearMap => linearMap direction) hPhysicalTransport
  have hDiffeomorphismGraphDirection :=
    congrArg (fun linearMap => linearMap direction) hDiffeomorphismGraphTransport
  have hAbelianDirection :=
    congrArg (fun linearMap => linearMap direction) hAbelianTransport
  simp only [ContinuousLinearMap.comp_apply] at hPhysicalDirection hDiffeomorphismGraphDirection hAbelianDirection
  have hPhysicalEuler :
      (globalCandidateALocalEulerLagrangeOperator period hPeriod
          (MinimalChart period hPeriod configuration data analysis firstChartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis firstChartData firstState))
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis firstChartData direction) =
        (globalCandidateALocalEulerLagrangeOperator period hPeriod
          (MinimalChart period hPeriod configuration data analysis secondChartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis secondChartData secondState))
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis secondChartData
              (transport direction)) := by
    calc
      _ = (globalCandidateALocalEulerLagrangeOperator period hPeriod
          (MinimalChart period hPeriod configuration data analysis secondChartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis secondChartData secondState))
          (physicalTransition.derivative
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
              hPeriod configuration data analysis firstChartData direction)) :=
        globalCandidateALocalEulerLagrangeOperator_transition_apply period hPeriod
          physicalTransition _
      _ = _ := congrArg
        (globalCandidateALocalEulerLagrangeOperator period hPeriod
          (MinimalChart period hPeriod configuration data analysis secondChartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis secondChartData secondState))
        hPhysicalDirection.symm
  have hDiffeomorphismGraphEuler := congrArg₂
    (fun state direction =>
      globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings (globalCandidateAMetricBySector period hPeriod data) state direction)
    hDiffeomorphismGraphState hDiffeomorphismGraphDirection.symm
  have hAbelianEuler := congrArg₂
    (fun state direction =>
      globalPairedAbelianOffShellHessian period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) state direction)
    hAbelianState hAbelianDirection.symm
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_apply,
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_apply]
  exact congrArg₂ (fun first second : Real => first + second)
    (congrArg₂ (fun first second : Real => first + second)
      hPhysicalEuler hDiffeomorphismGraphEuler)
    hAbelianEuler

/-- Criticality is invariant under every supplied projection-compatible
bounded linear equivalence. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_eq_zero_iff_projection_compatible
    (physicalTransition :
      GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis firstChartData)
        (MinimalChart period hPeriod configuration data analysis secondChartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis firstChartData firstState)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis secondChartData secondState))
    (transport :
      FullChart period hPeriod configuration data analysis firstChartData ≃L[Real]
        FullChart period hPeriod configuration data analysis secondChartData)
    (hDiffeomorphismGraphState :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData secondState)
    (hAbelianState :
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData secondState)
    (hPhysicalTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        physicalTransition.derivative.toContinuousLinearMap.comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis firstChartData))
    (hDiffeomorphismGraphTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData)
    (hAbelianTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis firstChartData firstState = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis secondChartData secondState = 0 := by
  have hCovariance :=
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_transition_of_projection_compatible
      period hPeriod configuration data analysis firstChartData secondChartData
      firstState secondState physicalTransition transport hDiffeomorphismGraphState
      hAbelianState hPhysicalTransport hDiffeomorphismGraphTransport hAbelianTransport
  constructor
  · intro hFirst
    apply ContinuousLinearMap.ext
    intro secondDirection
    obtain ⟨firstDirection, rfl⟩ := transport.surjective secondDirection
    have hAtDirection := congrArg (fun linearMap => linearMap firstDirection) hCovariance
    change
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis firstChartData firstState firstDirection =
        globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis secondChartData secondState
            (transport firstDirection) at hAtDirection
    rw [hFirst] at hAtDirection
    exact hAtDirection.symm
  · intro hSecond
    apply ContinuousLinearMap.ext
    intro firstDirection
    have hAtDirection := congrArg (fun linearMap => linearMap firstDirection) hCovariance
    change
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis firstChartData firstState firstDirection =
        globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis secondChartData secondState
            (transport firstDirection) at hAtDirection
    rw [hSecond] at hAtDirection
    exact hAtDirection

/-- The fixed-ambient full-BRST critical equation has the same truth value in
both projection-compatible charts. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_projection_compatible
    (physicalTransition :
      GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis firstChartData)
        (MinimalChart period hPeriod configuration data analysis secondChartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis firstChartData firstState)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis secondChartData secondState))
    (transport :
      FullChart period hPeriod configuration data analysis firstChartData ≃L[Real]
        FullChart period hPeriod configuration data analysis secondChartData)
    (hDiffeomorphismGraphState :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData secondState)
    (hAbelianState :
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData secondState)
    (hPhysicalTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        physicalTransition.derivative.toContinuousLinearMap.comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis firstChartData))
    (hDiffeomorphismGraphTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData)
    (hAbelianTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis firstChartData firstState = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis secondChartData secondState = 0 := by
  rw [← global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate,
    ← global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_eq_zero_iff_projection_compatible
      period hPeriod configuration data analysis firstChartData secondChartData
      firstState secondState physicalTransition transport hDiffeomorphismGraphState
      hAbelianState hPhysicalTransport hDiffeomorphismGraphTransport hAbelianTransport

/-- Gate 270: exact action, Euler-covector and critical-locus covariance under
every supplied projection-compatible bounded chart transport. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_projection_compatible_chart_covariance_gate
    (physicalTransition :
      GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis firstChartData)
        (MinimalChart period hPeriod configuration data analysis secondChartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis firstChartData firstState)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
          hPeriod configuration data analysis secondChartData secondState))
    (transport :
      FullChart period hPeriod configuration data analysis firstChartData ≃L[Real]
        FullChart period hPeriod configuration data analysis secondChartData)
    (hDiffeomorphismGraphState :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData secondState)
    (hAbelianState :
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData secondState)
    (hPhysicalTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        physicalTransition.derivative.toContinuousLinearMap.comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalProjection period
            hPeriod configuration data analysis firstChartData))
    (hDiffeomorphismGraphTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGraphProjection
          period hPeriod configuration data analysis firstChartData)
    (hAbelianTransport :
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis secondChartData).comp
          transport.toContinuousLinearMap =
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
          configuration data analysis firstChartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
          data analysis firstChartData firstState =
        globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod configuration
          data analysis secondChartData secondState ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis firstChartData firstState =
        (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis secondChartData secondState).comp
            transport.toContinuousLinearMap ∧
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
            period hPeriod configuration data analysis firstChartData firstState = 0 ↔
        globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
            period hPeriod configuration data analysis secondChartData secondState = 0) := by
  exact ⟨
    globalCandidateAGaugeFixedNonlinearFullBRSTAction_eq_of_projection_compatible
      period hPeriod configuration data analysis firstChartData secondChartData
      firstState secondState physicalTransition hDiffeomorphismGraphState hAbelianState,
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_transition_of_projection_compatible
      period hPeriod configuration data analysis firstChartData secondChartData
      firstState secondState physicalTransition transport hDiffeomorphismGraphState
      hAbelianState hPhysicalTransport hDiffeomorphismGraphTransport hAbelianTransport,
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_projection_compatible
      period hPeriod configuration data analysis firstChartData secondChartData
      firstState secondState physicalTransition transport hDiffeomorphismGraphState
      hAbelianState hPhysicalTransport hDiffeomorphismGraphTransport hAbelianTransport⟩

end Covariance
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleChartCovariance4D
end JanusFormal
