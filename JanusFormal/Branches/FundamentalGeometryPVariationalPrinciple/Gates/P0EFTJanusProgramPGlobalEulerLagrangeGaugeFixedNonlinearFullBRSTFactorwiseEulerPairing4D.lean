import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D

/-!
# Factorwise Euler pairing for the nonlinear full-BRST chart

The core first variation is the exact sum of its physical Euler contribution
and two factor Hessian pairings, whose strong Riesz representatives are
already established in the factor modules.  Keeping the three scalars
separate avoids asserting a total Riesz representative for the non-complete
relational chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldFactorwise :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceFactorwise :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldFactorwise :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceFactorwise :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceFactorwise :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteFactorwise :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section FactorwiseEuler

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

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev FullCore :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupFactorwise :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleFactorwise :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

/-- Physical Euler contribution evaluated on the physical projection of one
full-core test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution
    (state : FullChart period hPeriod configuration data analysis chartData)
    (core : FullCore period hPeriod configuration) : Real :=
  globalCandidateALocalEulerLagrangeOperator period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
          period hPeriod configuration data analysis chartData state))
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
            period hPeriod configuration data core)))

/-- Diffeomorphism-BRST Hessian pairing on one full-core test.  Its strong
Riesz representation is the already established factor theorem. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
    (state : FullChart period hPeriod configuration data analysis chartData)
    (core : FullCore period hPeriod configuration) : Real :=
  globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
      period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
        period hPeriod configuration data analysis chartData state))
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
      period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
          period hPeriod configuration data core)))

/-- Paired-Abelian BRST Hessian pairing on one full-core test.  Its strong
Riesz representation is the already established factor theorem. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution
    (state : FullChart period hPeriod configuration data analysis chartData)
    (core : FullCore period hPeriod configuration) : Real :=
  globalPairedAbelianOffShellHessian period hPeriod
    (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
      configuration data analysis chartData state)
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data) core.2.2)

/-- Exact factorwise first variation: physical Euler plus the two completed
BRST Riesz pairings. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise
    (state : FullChart period hPeriod configuration data analysis chartData)
    (core : FullCore period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state core =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution
          period hPeriod configuration data analysis chartData state core +
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
          period hPeriod configuration data analysis chartData state core +
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution
          period hPeriod configuration data analysis chartData state core := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_coupled]
  simp only [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTEulerOperator,
    add_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Weak factorwise form of the exact full-BRST Euler equation. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTFactorwiseEulerEquationAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  ∀ core : FullCore period hPeriod configuration,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution period
          hPeriod configuration data analysis chartData state core +
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
          period hPeriod configuration data analysis chartData state core +
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution
          period hPeriod configuration data analysis chartData state core = 0

theorem globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_eq_zero_iff_factorwise
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFactorwiseEulerEquationAt
        period hPeriod configuration data analysis chartData state := by
  constructor
  · intro hZero core
    have hApply := congrArg (fun covector => covector core) hZero
    rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise]
      at hApply
    simpa using hApply
  · intro hFactorwise
    apply LinearMap.ext
    intro core
    rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise]
    exact hFactorwise core

/-- Exact criticality is equivalent to the factorwise physical/diffeomorphism/
Abelian weak equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_factorwise
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFactorwiseEulerEquationAt
        period hPeriod configuration data analysis chartData state := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_eq_zero_iff_core,
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_eq_zero_iff_factorwise]

/-- Gate 225: the exact nonlinear full-BRST Euler equation has its canonical
factorwise weak pairing, without a total relational Riesz claim. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_factorwise_euler_pairing_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFactorwiseEulerEquationAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_factorwise period
    hPeriod configuration data analysis chartData state

end FactorwiseEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D
end JanusFormal
