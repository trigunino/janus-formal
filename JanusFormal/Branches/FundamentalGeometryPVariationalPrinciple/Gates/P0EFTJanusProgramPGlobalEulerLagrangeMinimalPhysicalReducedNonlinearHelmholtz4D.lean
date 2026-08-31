import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertNineBlockLinearization4D

/-!
# Nonlinear Helmholtz symmetry on the reduced physical Hilbert space

On the admissible reduced domain, the Euler covector is the actual gradient of
the reduced action and its Jacobian is the symmetric reduced Hessian.  The
strong Riesz linearization therefore has a symmetric Hilbert pairing.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHelmholtz4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertLinearization4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertNineBlockLinearization4D

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
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)

/-- Reduced states represented inside the genuine local action domain. -/
def globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain :
    Set (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :=
  {state | globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
    configuration data analysis chartData reducedChart state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain}

theorem globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_isOpen :
    IsOpen (globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period
      hPeriod configuration data analysis chartData reducedChart) := by
  apply (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData).isOpen_domain.preimage
  exact continuous_const.add
    (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period hPeriod
      configuration data analysis chartData reducedChart).continuous

theorem globalCandidateAMinimalPhysicalReducedHilbert_zero_mem_admissibleDomain :
    (0 : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period hPeriod
        configuration data analysis chartData reducedChart := by
  simp only [globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain,
    mem_setOf_eq, globalCandidateAMinimalPhysicalReducedHilbertChartPoint,
    map_zero, add_zero]
  exact (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData).chartBridge.basePoint_mem

/-- On the admissible domain, the reduced Euler covector is the actual Frechet
gradient of the reduced action. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertActionGradient_eq_euler
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period hPeriod
        configuration data analysis chartData reducedChart) :
    actionGradient
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis chartData reducedChart) state =
      globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart state := by
  exact globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv period hPeriod
    configuration data analysis chartData reducedChart state hState

/-- Pointwise nonlinear Helmholtz symmetry of the actual reduced Euler
covector. -/
theorem globalCandidateAMinimalPhysicalReducedHilbert_helmholtzJacobianAt
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period hPeriod
        configuration data analysis chartData reducedChart) :
    HelmholtzJacobianAt
      (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart) state := by
  intro first second
  rw [globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_fderiv period
    hPeriod configuration data analysis chartData reducedChart state hState]
  exact globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_symmetric
    period hPeriod configuration data analysis chartData reducedChart state
      hState first second

/-- Nonlinear Helmholtz symmetry holds on the whole admissible reduced
domain. -/
theorem globalCandidateAMinimalPhysicalReducedHilbert_helmholtzJacobianOn :
    HelmholtzJacobianOn
      (globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period
        hPeriod configuration data analysis chartData reducedChart)
      (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart) := by
  intro state hState
  exact globalCandidateAMinimalPhysicalReducedHilbert_helmholtzJacobianAt period
    hPeriod configuration data analysis chartData reducedChart state hState

/-- The strong reduced linearization is symmetric in Hilbert pairing. -/
theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing_symmetric
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain period hPeriod
        configuration data analysis chartData reducedChart)
    (first second : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData reducedChart state
            first) second =
      inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData reducedChart state
            second) first := by
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing,
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing]
  exact globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_symmetric
    period hPeriod configuration data analysis chartData reducedChart state
      hState first second

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHelmholtz4D
end JanusFormal
