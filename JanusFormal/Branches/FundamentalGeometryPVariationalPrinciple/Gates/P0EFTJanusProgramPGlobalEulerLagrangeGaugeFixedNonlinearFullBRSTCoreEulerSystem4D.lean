import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4DTerminal
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D

/-!
# Exact core Euler system for the nonlinear full-BRST chart

The exact first variation is pulled back along the bijective algebraic core.
Its three restrictions are the gauge-free physical, diffeomorphism
nonminimal, and paired Abelian equations.  The last equation remains coupled
to the physical direction through the unique shared Abelian potential; no
total Riesz or completeness assertion is made.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D

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
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldCoreEuler :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceCoreEuler :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldCoreEuler :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceCoreEuler :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceCoreEuler :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteCoreEuler :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section CoreEulerSystem

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

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev FullCore :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupCoreEuler :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleCoreEuler :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupCoreEuler :
    AddCommGroup
      (GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
        configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Exact first variation restricted to the algebraic full-BRST core. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    FullCore period hPeriod configuration →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
      configuration data analysis chartData state).toLinearMap.comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
      configuration data analysis chartData)

/-- Gauge-free physical restriction of the exact core first variation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
        configuration →ₗ[Real] Real :=
  productCovectorFirst
    (First := GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
      configuration)
    (Second := GlobalDiffeomorphismNonminimalFields period hPeriod ×
      GlobalPairedAbelianBRSTState period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
      configuration data analysis chartData state)

/-- Diffeomorphism-nonminimal restriction of the exact core first variation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalDiffeomorphismNonminimalFields period hPeriod →ₗ[Real] Real :=
  productCovectorFirst
    (First := GlobalDiffeomorphismNonminimalFields period hPeriod)
    (Second := GlobalPairedAbelianBRSTState period hPeriod)
    (productCovectorSecond
      (First := GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
        configuration)
      (Second := GlobalDiffeomorphismNonminimalFields period hPeriod ×
        GlobalPairedAbelianBRSTState period hPeriod)
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period
        hPeriod configuration data analysis chartData state))

/-- Paired Abelian restriction, including its shared physical-potential
contribution. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real] Real :=
  productCovectorSecond
    (First := GlobalDiffeomorphismNonminimalFields period hPeriod)
    (Second := GlobalPairedAbelianBRSTState period hPeriod)
    (productCovectorSecond
      (First := GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
        configuration)
      (Second := GlobalDiffeomorphismNonminimalFields period hPeriod ×
        GlobalPairedAbelianBRSTState period hPeriod)
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period
        hPeriod configuration data analysis chartData state))

/-- Three canonical restrictions of the coupled full-BRST Euler equation. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
      period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector
        period hPeriod configuration data analysis chartData state = 0

/-- Exact criticality for the already established full-BRST first
derivative. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
    configuration data analysis chartData state = 0

theorem globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_eq_zero_iff_components
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerSystemAt period
        hPeriod configuration data analysis chartData state := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerSystemAt
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector
  rw [productCovector_eq_zero_iff]
  rw [productCovector_eq_zero_iff]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_eq_zero_iff_core
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period
        hPeriod configuration data analysis chartData state = 0 := by
  constructor
  · intro hEuler
    apply LinearMap.ext
    intro core
    have hApply := congrArg
      (fun covector => covector
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period
          hPeriod configuration data analysis chartData core)) hEuler
    simpa [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector]
      using hApply
  · intro hCore
    apply ContinuousLinearMap.ext
    intro test
    rcases globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_surjective
      period hPeriod configuration data analysis chartData test with
      ⟨core, rfl⟩
    have hApply := congrArg (fun covector => covector core) hCore
    simpa [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector]
      using hApply

/-- The exact full-BRST Euler equation is equivalent to its three canonical
core restrictions. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coreEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerSystemAt period
        hPeriod configuration data analysis chartData state := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_eq_zero_iff_core,
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_eq_zero_iff_components]

/-- Evaluation on a core test is the coupled diffeomorphism/physical and
paired Abelian first variation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_coupled
    (state : FullChart period hPeriod configuration data analysis chartData)
    (core : FullCore period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state core =
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTEulerOperator
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
            period hPeriod configuration data analysis chartData state)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
            period hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
              period hPeriod configuration data core)) +
        globalPairedAbelianOffShellHessian period hPeriod
          (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
            hPeriod configuration data analysis chartData state)
          (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
            (BaseMetric period hPeriod configuration data) core.2.2) := by
  rfl

/-- Gate 224: exact criticality, its three core equations, and the coupled
core-test formula. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_core_euler_system_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerSystemAt period
        hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coreEulerSystem
    period hPeriod configuration data analysis chartData state

end CoreEulerSystem

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
end JanusFormal
