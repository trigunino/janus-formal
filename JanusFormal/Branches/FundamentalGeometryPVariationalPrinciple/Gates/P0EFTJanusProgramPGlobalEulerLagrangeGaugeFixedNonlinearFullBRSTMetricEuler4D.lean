import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

/-!
# Coupled full-BRST metric Euler equation

Pure metric tests expose the Einstein--Maxwell block, the remaining physical
metric cross-block and the diagonal diffeomorphism-BRST metric response.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldMetricEuler :
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

local instance effectiveQuotientChartedSpaceMetricEuler :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldMetricEuler :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceMetricEuler :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceMetricEuler :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceMetricEuler :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldMetricEuler :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceMetricEuler :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldMetricEuler :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteMetricEuler :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section MetricEuler

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

private abbrev GaugeFreePhysical :=
  GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupMetricEuler :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleMetricEuler :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupMetricEuler :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Pure metric directions regarded as gauge-free physical directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun metric :=
    ⟨globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
      configuration.physical metric, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (globalMetricPerturbationMinimalPhysicalTangentLinearMap period
      hPeriod configuration.physical).map_add first second
  map_smul' scalar metric := by
    apply Subtype.ext
    exact (globalMetricPerturbationMinimalPhysicalTangentLinearMap period
      hPeriod configuration.physical).map_smul scalar metric

/-- Full-BRST Euler covector restricted to pure metric tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap
        period hPeriod configuration)

/-- Minimal-physical part of a pure metric full-BRST test is the existing
metric Euler covector. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricPhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro metric
  rfl

/-- Diffeomorphism-BRST metric response restricted to pure metric tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap
        period hPeriod configuration)

/-- Exact metric equation: Einstein--Maxwell, the named physical cross-block
and the metric response of diffeomorphism BRST gauge fixing. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
            hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state) +
          globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
            period hPeriod configuration data analysis chartData state := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq]
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
  rw [LinearMap.add_comp]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricPhysicalEulerCovector_eq,
    globalCandidateAMinimalPhysicalMetricEulerCovector_decomposition]

/-- Full criticality forces the coupled metric equation, without forcing its
three summands to vanish separately. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_metricEuler_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
            hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state) +
          globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
            period hPeriod configuration data analysis chartData state = 0 := by
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq]
  have hCoupled :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  apply LinearMap.ext
  intro metric
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap
          period hPeriod configuration metric) = 0
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    hCoupled.1]
  rfl

/-- Gate 230: the full-BRST metric equation keeps every genuine coupled
contribution. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
            hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state) +
          globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
            period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq period hPeriod
    configuration data analysis chartData state

end MetricEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
