import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertBlockSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertNineBlockLinearization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHelmholtz4D

/-!
# Reduced nonlinear Euler operator from quotient-core closure

The unobstructed reduced dense-core closure constructs the reduced Hilbert
chart.  It therefore determines the exact nonlinear action, strong Euler--Riesz
residual, nine-block linearization, and Helmholtz symmetry without a separately
supplied chart equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertOfDenseCoreClosure4D

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
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertLinearization4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertNineBlockLinearization4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHelmholtz4D

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
    (closure : ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D
      period hPeriod configuration data analysis chartData)

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

/-- Reduced Hilbert chart constructed from the quotient-core closure packet. -/
def globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure :=
  globalCandidateAMinimalPhysicalReducedHilbertChartOfDenseCoreClosure period
    hPeriod configuration data analysis chartData closure

/-- Exact nonlinear action determined by the reduced dense-core closure. -/
def globalCandidateAMinimalPhysicalReducedHilbertAction_of_denseCoreClosure :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)

/-- Nonlinear Frechet Euler covector determined by the same closure. -/
noncomputable def globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
      state

/-- Strong nonlinear Euler residual determined by the same closure. -/
noncomputable def globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
      state

def globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure :
    Set (Reduced period hPeriod configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)

def GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_of_denseCoreClosure
    period hPeriod configuration data analysis chartData closure state = 0

theorem globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure_isOpen :
    IsOpen
      (globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure) := by
  exact globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_isOpen
    period hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)

theorem globalCandidateAMinimalPhysicalReducedHilbert_zero_mem_admissibleDomain_of_denseCoreClosure :
    (0 : Reduced period hPeriod configuration data analysis) ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure := by
  exact globalCandidateAMinimalPhysicalReducedHilbert_zero_mem_admissibleDomain
    period hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)

theorem globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction_of_denseCoreClosure
          period hPeriod configuration data analysis chartData closure)
        state =
      globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state := by
  exact globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv period
    hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
      state hState

/-- Strong Frechet--Riesz identity for the exact nonlinear action. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_fderiv_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
    (test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_of_denseCoreClosure
          period hPeriod configuration data analysis chartData closure state)
        test =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction_of_denseCoreClosure
          period hPeriod configuration data analysis chartData closure)
        state test := by
  unfold
    globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_of_denseCoreClosure
    globalCandidateAMinimalPhysicalReducedHilbertAction_of_denseCoreClosure
  unfold
    globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
    globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain at hState
  simp only [Set.mem_setOf_eq] at hState
  rw [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing]
  rw [globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv]
  exact hState

/-- Strong criticality is exactly the genuine weak eight-sector system. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_weakEightSectorSystem_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure) :
    GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state ↔
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis chartData
              (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
                period hPeriod configuration data analysis chartData closure)
              state) := by
  exact
    globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_weakEightSectorSystem
      period hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
          period hPeriod configuration data analysis chartData closure)
        state hState

/-- Nonlinear Helmholtz symmetry on the whole closure-derived domain. -/
theorem globalCandidateAMinimalPhysicalReducedHilbert_helmholtzJacobianOn_of_denseCoreClosure :
    HelmholtzJacobianOn
      (globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
      (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure) := by
  exact globalCandidateAMinimalPhysicalReducedHilbert_helmholtzJacobianOn period
    hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)

/-- The nonlinear strong linearization pairs as the genuine nine-block
Hessian, with the reduced chart itself derived from the closure. -/
theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing_eq_nineBlock_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
    (first second : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData
            (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
              period hPeriod configuration data analysis chartData closure)
            state first)
        second =
      globalCandidateAMinimalPhysicalReducedNineBlockHessian period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
            period hPeriod configuration data analysis chartData closure)
          state first second := by
  exact
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing_eq_nineBlock
      period hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
          period hPeriod configuration data analysis chartData closure)
        state hState first second

/-- Gate 199: quotient-core closure determines the exact nonlinear strong
Euler equation and its weak eight-sector content. -/
theorem candidate_a_reduced_nonlinear_euler_of_denseCoreClosure_gate
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure) :
    (∀ test : Reduced period hPeriod configuration data analysis,
      inner Real
          (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_of_denseCoreClosure
            period hPeriod configuration data analysis chartData closure state)
          test =
        fderiv Real
          (globalCandidateAMinimalPhysicalReducedHilbertAction_of_denseCoreClosure
            period hPeriod configuration data analysis chartData closure)
          state test) ∧
      (GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_of_denseCoreClosure
          period hPeriod configuration data analysis chartData closure state ↔
        GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
          configuration data analysis chartData
            (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
              hPeriod configuration data analysis chartData
                (globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure
                  period hPeriod configuration data analysis chartData closure)
                state)) := by
  constructor
  · intro test
    exact
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_fderiv_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state
          hState test
  · exact
      globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_weakEightSectorSystem_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state hState

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertOfDenseCoreClosure4D
end JanusFormal
