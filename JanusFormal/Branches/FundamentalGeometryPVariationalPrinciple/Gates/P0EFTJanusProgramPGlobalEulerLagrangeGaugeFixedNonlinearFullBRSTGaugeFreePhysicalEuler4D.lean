import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D

/-!
# Coupled Euler equation on the gauge-free physical tangent

Gauge-free physical tests retain the exact minimal-physical Euler covector and
the metric response of the diagonal diffeomorphism BRST Hessian.  Their paired
Abelian BRST contribution vanishes because no Abelian state is varied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D

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
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldGaugeFree :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpaceGaugeFree :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldGaugeFree :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceGaugeFree :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceGaugeFree :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceGaugeFree :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldGaugeFree :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceGaugeFree :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldGaugeFree :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteGaugeFree :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section GaugeFreePhysicalEuler

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

private abbrev GaugeFreePhysical :=
  GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
    configuration

private abbrev FullCore :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupGaugeFree :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleGaugeFree :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroup :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Gauge-free physical inclusion into the full-BRST algebraic core. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap :
    GaugeFreePhysical period hPeriod configuration →ₗ[Real]
      FullCore period hPeriod configuration where
  toFun physical := (physical, (0, 0))
  map_add' first second := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp
      · change (0 : GlobalPairedAbelianBRSTState period hPeriod) = 0 + 0
        simp
  map_smul' scalar physical := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp
      · change (0 : GlobalPairedAbelianBRSTState period hPeriod) = scalar • 0
        simp

/-- Minimal-physical action Euler covector restricted to gauge-free
directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GaugeFreePhysical period hPeriod configuration →ₗ[Real] Real :=
  ((globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
        configuration data analysis chartData state)).toLinearMap.comp
    (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
      configuration data analysis chartData).toLinearMap).comp
    (LinearMap.ker
      (globalCandidateAMinimalPhysicalGaugeCoefficientLinearMap period hPeriod
        configuration)).subtype

/-- Gauge-free physical direction viewed by the diagonal diffeomorphism BRST
graph through its metric component. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap :
    GaugeFreePhysical period hPeriod configuration →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun physical :=
    { metricPerturbation :=
        physical.1.1.completeVariation.fullMetricPerturbation
      nonminimal := 0 }
  map_add' first second := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · rfl
    · change (0 : GlobalDiffeomorphismNonminimalFields period hPeriod) =
          0 + 0
      simp
  map_smul' scalar physical := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · rfl
    · change (0 : GlobalDiffeomorphismNonminimalFields period hPeriod) =
          scalar • 0
      simp

/-- Metric-response part of the diffeomorphism BRST Hessian on gauge-free
physical tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GaugeFreePhysical period hPeriod configuration →ₗ[Real] Real :=
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)).toLinearMap.comp
      ((globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
        hPeriod (BaseMetric period hPeriod configuration data)).comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
            period hPeriod configuration))

private theorem physicalEulerContribution_gaugeFreeOnly_eq
    (state : FullChart period hPeriod configuration data analysis chartData)
    (physical : GaugeFreePhysical period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap
          period hPeriod configuration physical) =
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
        period hPeriod configuration data analysis chartData state physical := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection_core]
  have hPhysicalTangent :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap
          period hPeriod configuration physical)).1 = physical.1 := by
    change physical.1 +
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
        hPeriod data 0 = physical.1
    rw [map_zero, add_zero]
  rw [hPhysicalTangent]
  rfl

private theorem diffeomorphismState_gaugeFreeOnly_eq
    (physical : GaugeFreePhysical period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap period
        hPeriod configuration
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
          period hPeriod configuration data
          (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap
            period hPeriod configuration physical)) =
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
        period hPeriod configuration physical := by
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · change
      (physical.1 +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data 0).1.completeVariation.fullMetricPerturbation =
        physical.1.1.completeVariation.fullMetricPerturbation
    rw [map_zero, add_zero]
  · rfl

private theorem diffeomorphismBRSTContribution_gaugeFreeOnly_eq
    (state : FullChart period hPeriod configuration data analysis chartData)
    (physical : GaugeFreePhysical period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap
          period hPeriod configuration physical) =
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state physical := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection_core,
    diffeomorphismState_gaugeFreeOnly_eq]
  rfl

private theorem abelianBRSTContribution_gaugeFreeOnly_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (physical : GaugeFreePhysical period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap
          period hPeriod configuration physical) = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution
  change
    globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (BaseMetric period hPeriod configuration data) 0) = 0
  rw [map_zero, map_zero]

/-- Exact gauge-free equation: minimal-physical Euler plus the metric response
of diffeomorphism BRST gauge fixing. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
          period hPeriod configuration data analysis chartData state +
        globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
          period hPeriod configuration data analysis chartData state := by
  apply LinearMap.ext
  intro physical
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalOnlyCoreLinearMap
          period hPeriod configuration physical) = _
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise,
    physicalEulerContribution_gaugeFreeOnly_eq,
    diffeomorphismBRSTContribution_gaugeFreeOnly_eq,
    abelianBRSTContribution_gaugeFreeOnly_eq_zero]
  simp

/-- The metric BRST response keeps the existing factorwise strong Riesz
pairing. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector_apply_eq_rieszPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (physical : GaugeFreePhysical period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state physical =
      inner Real
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period
          hPeriod couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint
            period hPeriod configuration data analysis chartData state))
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
          hPeriod (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
            period hPeriod configuration physical)) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
  simp only [LinearMap.comp_apply]
  exact (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing
    period hPeriod couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
      hPeriod (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
        period hPeriod configuration physical))).symm

/-- Fully resolved algebraic core system, retaining the honest physical/BRST
metric coupling. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTCoupledCoreEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
        period hPeriod configuration data analysis chartData state +
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0

/-- Exact criticality is equivalent to the coupled resolved core system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTCoupledCoreEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_resolvedCoreEulerSystem]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTResolvedCoreEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCoupledCoreEulerSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq]

/-- Gate 229: the gauge-free physical equation retains exactly its diagonal
diffeomorphism-BRST metric response. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_gaugeFree_physical_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTCoupledCoreEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
    period hPeriod configuration data analysis chartData state

end GaugeFreePhysicalEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D
end JanusFormal
