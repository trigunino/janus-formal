import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D

/-!
# Chart transition for the nonlinear Hilbert Euler residual

Compatible bounded realizations of the common Hilbert space give the same
pulled Euler covector and Riesz residual on a genuine variational overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertChartTransition4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

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
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D

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
    (first second : GlobalCandidateALocalVariationalChart period hPeriod
      couplings NonNullFace NullFace measure)
    (firstBase : first.Model) (secondBase : second.Model)
    (firstRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        first.Model)
    (secondRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        second.Model)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)

private abbrev FirstPoint :=
  globalCandidateANonlinearHilbertChartPoint period hPeriod configuration data
    analysis first firstBase firstRealization state

private abbrev SecondPoint :=
  globalCandidateANonlinearHilbertChartPoint period hPeriod configuration data
    analysis second secondBase secondRealization state

/-- The pulled nonlinear actions agree at the represented overlap state. -/
theorem globalCandidateANonlinearHilbertAction_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second
        (FirstPoint period hPeriod configuration data analysis first firstBase
          firstRealization state)
        (SecondPoint period hPeriod configuration data analysis second secondBase
          secondRealization state)) :
    globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis first firstBase firstRealization state =
      globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis second secondBase secondRealization state := by
  have hAction := transition.action_eventuallyEq.self_of_nhds
  change globalCandidateALocalActionPullback period hPeriod first
      (FirstPoint period hPeriod configuration data analysis first firstBase
        firstRealization state) =
    globalCandidateALocalActionPullback period hPeriod second
      (SecondPoint period hPeriod configuration data analysis second secondBase
        secondRealization state)
  simpa only [Function.comp_apply, transition.maps_point] using hAction

/-- Compatible chart derivatives make the pulled Euler covectors identical. -/
theorem globalCandidateANonlinearHilbertEulerCovector_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second
        (FirstPoint period hPeriod configuration data analysis first firstBase
          firstRealization state)
        (SecondPoint period hPeriod configuration data analysis second secondBase
          secondRealization state))
    (hRealization : transition.derivative.toContinuousLinearMap.comp
      firstRealization = secondRealization) :
    globalCandidateANonlinearHilbertEulerCovector period hPeriod configuration
        data analysis first firstBase firstRealization state =
      globalCandidateANonlinearHilbertEulerCovector period hPeriod configuration
        data analysis second secondBase secondRealization state := by
  apply ContinuousLinearMap.ext
  intro direction
  change globalCandidateALocalEulerLagrangeOperator period hPeriod first
      (FirstPoint period hPeriod configuration data analysis first firstBase
        firstRealization state) (firstRealization direction) =
    globalCandidateALocalEulerLagrangeOperator period hPeriod second
      (SecondPoint period hPeriod configuration data analysis second secondBase
        secondRealization state) (secondRealization direction)
  calc
    _ = globalCandidateALocalEulerLagrangeOperator period hPeriod second
        (SecondPoint period hPeriod configuration data analysis second secondBase
          secondRealization state)
        (transition.derivative (firstRealization direction)) :=
      globalCandidateALocalEulerLagrangeOperator_transition_apply period hPeriod
        transition (firstRealization direction)
    _ = _ := by
      have hApply := congrArg (fun map => map direction) hRealization
      have hDirection :
          transition.derivative (firstRealization direction) =
            secondRealization direction := by
        change transition.derivative.toContinuousLinearMap
          (firstRealization direction) = secondRealization direction
        simpa only [ContinuousLinearMap.comp_apply] using hApply
      rw [hDirection]

/-- Hence the strong nonlinear Riesz residual is chart-independent. -/
theorem globalCandidateANonlinearHilbertRieszResidual_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second
        (FirstPoint period hPeriod configuration data analysis first firstBase
          firstRealization state)
        (SecondPoint period hPeriod configuration data analysis second secondBase
          secondRealization state))
    (hRealization : transition.derivative.toContinuousLinearMap.comp
      firstRealization = secondRealization) :
    globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis first firstBase firstRealization state =
      globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis second secondBase secondRealization state := by
  unfold globalCandidateANonlinearHilbertRieszResidual
  rw [globalCandidateANonlinearHilbertEulerCovector_transition period hPeriod
    configuration data analysis first second firstBase secondBase firstRealization
      secondRealization state transition hRealization]

/-- Stationarity of the pulled nonlinear action is invariant on the overlap. -/
theorem globalCandidateANonlinearHilbertAction_fderiv_eq_zero_iff_transition
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second
        (FirstPoint period hPeriod configuration data analysis first firstBase
          firstRealization state)
        (SecondPoint period hPeriod configuration data analysis second secondBase
          secondRealization state))
    (hRealization : transition.derivative.toContinuousLinearMap.comp
      firstRealization = secondRealization) :
    fderiv Real
        (globalCandidateANonlinearHilbertAction period hPeriod configuration data
          analysis first firstBase firstRealization) state = 0 ↔
      fderiv Real
        (globalCandidateANonlinearHilbertAction period hPeriod configuration data
          analysis second secondBase secondRealization) state = 0 := by
  rw [globalCandidateANonlinearHilbertAction_fderiv_eq_zero_iff_rieszResidual
      period hPeriod configuration data analysis first firstBase firstRealization
        state transition.first_mem_domain,
    globalCandidateANonlinearHilbertAction_fderiv_eq_zero_iff_rieszResidual
      period hPeriod configuration data analysis second secondBase
        secondRealization state transition.second_mem_domain,
    globalCandidateANonlinearHilbertRieszResidual_transition period hPeriod
      configuration data analysis first second firstBase secondBase
        firstRealization secondRealization state transition hRealization]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertChartTransition4D
end JanusFormal
