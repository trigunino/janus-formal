import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertOfDenseCoreClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

/-!
# Reduced nonlinear Euler equation as a componentwise PDE system

The reduced quotient-core closure gives the exact nonlinear strong residual.
At every represented state, its vanishing is equivalent to any supplied set
of eight separating componentwise PDE residuals for the same local Euler
covector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertComponentwisePDEOfDenseCoreClosure4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertOfDenseCoreClosure4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

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

private abbrev ClosureChart :=
  globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure period
    hPeriod configuration data analysis chartData closure

private abbrev ClosureChartPoint
    (state : Reduced period hPeriod configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
    configuration data analysis chartData
      (ClosureChart period hPeriod configuration data analysis chartData
        closure) state

/-- Closure-derived strong criticality is exactly any supplied separating
componentwise PDE realization of the same local Euler covector. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_componentwiseStrongPDE_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData
        (ClosureChartPoint period hPeriod configuration data analysis chartData
          closure state)) :
    GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis chartData
          (ClosureChartPoint period hPeriod configuration data analysis chartData
            closure state) pdeData := by
  change
    GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period hPeriod
        configuration data analysis chartData
          (ClosureChart period hPeriod configuration data analysis chartData
            closure) state ↔ _
  exact
    (globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_localEuler
      period hPeriod configuration data analysis chartData
        (ClosureChart period hPeriod configuration data analysis chartData
          closure) state).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
        period hPeriod configuration data analysis chartData
          (ClosureChartPoint period hPeriod configuration data analysis chartData
            closure state) pdeData)

/-- Gate 204: the closure-derived nonlinear Riesz residual is the Frechet
gradient on the admissible domain and its zero set is the supplied eight-PDE
system. -/
theorem candidate_a_reduced_nonlinear_componentwise_pde_of_denseCoreClosure_gate
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData
        (ClosureChartPoint period hPeriod configuration data analysis chartData
          closure state)) :
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
        GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
          hPeriod configuration data analysis chartData
            (ClosureChartPoint period hPeriod configuration data analysis
              chartData closure state) pdeData) := by
  constructor
  · intro test
    exact
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_fderiv_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state
          hState test
  · exact
      globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_componentwiseStrongPDE_of_denseCoreClosure
        period hPeriod configuration data analysis chartData closure state pdeData

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertComponentwisePDEOfDenseCoreClosure4D
end JanusFormal
