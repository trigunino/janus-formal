import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D

/-!
# Chart transition for the reduced nonlinear Hilbert Euler residual

Two compatible local charts realized on the same reduced physical Hilbert
space define the same pulled action, Euler covector, Riesz residual and
stationarity equation on a genuine overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertChartTransition4D

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

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (firstChartData secondChartData :
      ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
        (measure := measure) configuration data analysis)
    (firstReducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
      period hPeriod configuration data analysis firstChartData)
    (secondReducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
      period hPeriod configuration data analysis secondChartData)
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)

private abbrev FirstChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis firstChartData

private abbrev SecondChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis secondChartData

private abbrev FirstPoint :=
  globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
    configuration data analysis firstChartData firstReducedChart state

private abbrev SecondPoint :=
  globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
    configuration data analysis secondChartData secondReducedChart state

/-- The two reduced pullbacks have the same action value on an overlap. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertAction_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (FirstChart period hPeriod configuration data analysis firstChartData)
      (SecondChart period hPeriod configuration data analysis secondChartData)
      (FirstPoint period hPeriod configuration data analysis firstChartData
        firstReducedChart state)
      (SecondPoint period hPeriod configuration data analysis secondChartData
        secondReducedChart state)) :
    globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
        configuration data analysis firstChartData firstReducedChart state =
      globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
        configuration data analysis secondChartData secondReducedChart state := by
  have hAction := transition.action_eventuallyEq.self_of_nhds
  change globalCandidateALocalActionPullback period hPeriod
      (FirstChart period hPeriod configuration data analysis firstChartData)
      (FirstPoint period hPeriod configuration data analysis firstChartData
        firstReducedChart state) =
    globalCandidateALocalActionPullback period hPeriod
      (SecondChart period hPeriod configuration data analysis secondChartData)
      (SecondPoint period hPeriod configuration data analysis secondChartData
        secondReducedChart state)
  simpa only [Function.comp_apply, transition.maps_point] using hAction

/-- Compatibility of the chart derivatives identifies the two pulled Euler
covectors on the common reduced carrier. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (FirstChart period hPeriod configuration data analysis firstChartData)
      (SecondChart period hPeriod configuration data analysis secondChartData)
      (FirstPoint period hPeriod configuration data analysis firstChartData
        firstReducedChart state)
      (SecondPoint period hPeriod configuration data analysis secondChartData
        secondReducedChart state))
    (hRealization : transition.derivative.toContinuousLinearMap.comp
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis firstChartData firstReducedChart) =
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis secondChartData secondReducedChart) :
    globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis firstChartData firstReducedChart state =
      globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis secondChartData secondReducedChart state := by
  apply ContinuousLinearMap.ext
  intro direction
  change globalCandidateALocalEulerLagrangeOperator period hPeriod
      (FirstChart period hPeriod configuration data analysis firstChartData)
      (FirstPoint period hPeriod configuration data analysis firstChartData
        firstReducedChart state)
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis firstChartData firstReducedChart
          direction) =
    globalCandidateALocalEulerLagrangeOperator period hPeriod
      (SecondChart period hPeriod configuration data analysis secondChartData)
      (SecondPoint period hPeriod configuration data analysis secondChartData
        secondReducedChart state)
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis secondChartData secondReducedChart
          direction)
  calc
    _ = globalCandidateALocalEulerLagrangeOperator period hPeriod
        (SecondChart period hPeriod configuration data analysis secondChartData)
        (SecondPoint period hPeriod configuration data analysis secondChartData
          secondReducedChart state)
        (transition.derivative
          (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
            hPeriod configuration data analysis firstChartData firstReducedChart
              direction)) :=
      globalCandidateALocalEulerLagrangeOperator_transition_apply period hPeriod
        transition _
    _ = _ := by
      have hApply := congrArg (fun map ↦ map direction) hRealization
      have hDirection :
          transition.derivative
              (globalCandidateAMinimalPhysicalReducedHilbertChartRealization
                period hPeriod configuration data analysis firstChartData
                  firstReducedChart direction) =
            globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
              hPeriod configuration data analysis secondChartData
                secondReducedChart direction := by
        change transition.derivative.toContinuousLinearMap
            (globalCandidateAMinimalPhysicalReducedHilbertChartRealization
              period hPeriod configuration data analysis firstChartData
                firstReducedChart direction) = _
        simpa only [ContinuousLinearMap.comp_apply] using hApply
      rw [hDirection]

/-- The strong reduced nonlinear Riesz residual is chart-independent. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (FirstChart period hPeriod configuration data analysis firstChartData)
      (SecondChart period hPeriod configuration data analysis secondChartData)
      (FirstPoint period hPeriod configuration data analysis firstChartData
        firstReducedChart state)
      (SecondPoint period hPeriod configuration data analysis secondChartData
        secondReducedChart state))
    (hRealization : transition.derivative.toContinuousLinearMap.comp
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis firstChartData firstReducedChart) =
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis secondChartData secondReducedChart) :
    globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
        configuration data analysis firstChartData firstReducedChart state =
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
        configuration data analysis secondChartData secondReducedChart state := by
  unfold globalCandidateAMinimalPhysicalReducedHilbertRieszResidual
  rw [globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_transition
    period hPeriod configuration data analysis firstChartData secondChartData
      firstReducedChart secondReducedChart state transition hRealization]

/-- Frechet stationarity is invariant under the reduced chart transition. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_eq_zero_iff_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (FirstChart period hPeriod configuration data analysis firstChartData)
      (SecondChart period hPeriod configuration data analysis secondChartData)
      (FirstPoint period hPeriod configuration data analysis firstChartData
        firstReducedChart state)
      (SecondPoint period hPeriod configuration data analysis secondChartData
        secondReducedChart state))
    (hRealization : transition.derivative.toContinuousLinearMap.comp
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis firstChartData firstReducedChart) =
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis secondChartData secondReducedChart) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis firstChartData firstReducedChart) state = 0 ↔
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis secondChartData secondReducedChart) state = 0 := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_eq_zero_iff_residual
      period hPeriod configuration data analysis firstChartData firstReducedChart
        state transition.first_mem_domain,
    globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_eq_zero_iff_residual
      period hPeriod configuration data analysis secondChartData
        secondReducedChart state transition.second_mem_domain]
  unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical
  rw [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_transition period
    hPeriod configuration data analysis firstChartData secondChartData
      firstReducedChart secondReducedChart state transition hRealization]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertChartTransition4D
end JanusFormal
