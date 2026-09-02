import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D

/-!
# Augmented graph-Riesz residual of the full-BRST metric equation

The genuine diagonal diffeomorphism-BRST graph is retained as the Hilbert
coordinate. The Einstein--Maxwell and physical cross-block covectors form the
scalar remainder. This is exact and separating, but it is not a local metric
PDE or a fixed-domain tensorial residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldMetricAugmentedResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceMetricAugmentedResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldMetricAugmentedResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceMetricAugmentedResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceMetricAugmentedResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section MetricAugmentedResidual

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

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

private abbrev PhysicalPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
    configuration data analysis chartData state

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

attribute [local instance 10001]
  diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
  diagonalGraphNormedSpaceDiffeomorphismGhostResidual
  diagonalGraphContinuousAddDiffeomorphismGhostResidual
  diagonalGraphModuleDiffeomorphismGhostResidual
  diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual
attribute [local instance 10002]
  diagonalGraphAddCommGroupDiffeomorphismGhostResidual
  diagonalGraphTopologicalSpaceDiffeomorphismGhostResidual
attribute [local instance]
  diagonalGraphIsBoundedSMulDiffeomorphismGhostResidual
  diagonalGraphUniformContinuousConstSMulDiffeomorphismGhostResidual
  diagonalGraphContinuousConstSMulDiffeomorphismGhostResidual
  diagonalGraphCompleteSpaceDiffeomorphismGhostResidual

/-- Data specialized to the authentic diagonal BRST graph. -/
structure DiagonalDiffeomorphismAugmentedGraphRieszData
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test] where
  baseMap : Test →ₗ[Real]
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric
  remainder : Test →ₗ[Real] Real
  baseCovector :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric →L[Real] Real

def DiagonalDiffeomorphismAugmentedGraphRieszData.toStateDependent
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test]
    (graphData : DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      metric Test) :=
  @StateDependentAugmentedGraphRieszData.mk Test
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric)
    inferInstance inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
      metric)
    graphData.baseMap graphData.remainder graphData.baseCovector

abbrev DiagonalDiffeomorphismAugmentedGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test]
    (graphData : DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      metric Test) :=
  @StateDependentAugmentedGraphHilbert Test
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric)
    inferInstance inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
      metric)
    (graphData.toStateDependent period hPeriod metric Test)

def diagonalDiffeomorphismAugmentedGraphRieszResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test]
    (graphData : DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      metric Test) :
    DiagonalDiffeomorphismAugmentedGraphHilbert period hPeriod metric Test
      graphData :=
  @stateDependentAugmentedGraphRieszResidual Test
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric)
    inferInstance inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphCompleteSpaceDiffeomorphismGhostResidual period hPeriod metric)
    (graphData.toStateDependent period hPeriod metric Test)

def diagonalDiffeomorphismAugmentedTotalCovector
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test]
    (graphData : DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      metric Test) : Test →ₗ[Real] Real :=
  @stateDependentAugmentedTotalCovector Test
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric)
    inferInstance inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
      metric)
    (graphData.toStateDependent period hPeriod metric Test)

theorem diagonalDiffeomorphismAugmentedTotalCovector_eq_zero_iff_graphResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test]
    (graphData : DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      metric Test) :
    diagonalDiffeomorphismAugmentedTotalCovector period hPeriod metric Test
          graphData = 0 ↔
      diagonalDiffeomorphismAugmentedGraphRieszResidual period hPeriod metric
        Test graphData = 0 :=
  @stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual Test
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric)
    inferInstance inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
      metric)
    (diagonalGraphCompleteSpaceDiffeomorphismGhostResidual period hPeriod metric)
    (graphData.toStateDependent period hPeriod metric Test)

/-- Pure physical metric tests mapped into the authentic diagonal BRST graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (BaseMetric period hPeriod configuration data) :=
  (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data)).comp
    ((globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
      period hPeriod configuration).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap period
        hPeriod configuration))

/-- Authentic Riesz representative of the diagonal BRST Hessian. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismAuthenticRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (BaseMetric period hPeriod configuration data) :=
  globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector_apply_eq_authenticRieszPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state test =
      inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismAuthenticRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap
          period hPeriod configuration data test) := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismAuthenticRieszResidual
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap
  simp only [LinearMap.comp_apply]
  exact
    (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing period
      hPeriod couplings (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
        hPeriod configuration data analysis chartData state)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
        hPeriod (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
          period hPeriod configuration
          (globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap
            period hPeriod configuration test)))).symm

/-- Authentic BRST graph coordinate plus the two physical metric covectors. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      (BaseMetric period hPeriod configuration data)
      (GlobalMinimalPhysicalMetricTest period hPeriod) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap
      period hPeriod configuration data
  remainder :=
    globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
        period hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) +
      globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state)
  baseCovector :=
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
      couplings (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
        hPeriod configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  DiagonalDiffeomorphismAugmentedGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)
    (GlobalMinimalPhysicalMetricTest period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphHilbert period
      hPeriod configuration data analysis chartData state :=
  diagonalDiffeomorphismAugmentedGraphRieszResidual period hPeriod
    (BaseMetric period hPeriod configuration data)
    (GlobalMinimalPhysicalMetricTest period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real] Real :=
  diagonalDiffeomorphismAugmentedTotalCovector period hPeriod
    (BaseMetric period hPeriod configuration data)
    (GlobalMinimalPhysicalMetricTest period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector_eq_baseCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state =
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData period
        hPeriod configuration data analysis chartData state).baseCovector.toLinearMap.comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap
          period hPeriod configuration data) := by
  apply LinearMap.ext
  intro test
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_augmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedTotalCovector
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector_eq_baseCovector]
  apply LinearMap.ext
  intro test
  simp [globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedTotalCovector,
    diagonalDiffeomorphismAugmentedTotalCovector,
    DiagonalDiffeomorphismAugmentedGraphRieszData.toStateDependent,
    stateDependentAugmentedTotalCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData]
  · abel

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_augmentedTotalCovector]
  exact
    diagonalDiffeomorphismAugmentedTotalCovector_eq_zero_iff_graphResidual
      period hPeriod (BaseMetric period hPeriod configuration data)
      (GlobalMinimalPhysicalMetricTest period hPeriod)
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData period
        hPeriod configuration data analysis chartData state)

/-- Gate256's system with the metric scalar certificate strengthened to the
authentic diagonal-BRST augmented graph residual. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphResidualEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphRieszResidual
          period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
              period hPeriod configuration data analysis chartData state = 0 ∧
            globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
                period hPeriod configuration data analysis chartData state = 0 ∧
              globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual
                  period hPeriod configuration data analysis chartData state = 0 ∧
                GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
                    period hPeriod configuration data analysis chartData state ∧
                  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
                      period hPeriod configuration data analysis chartData state = 0 ∧
                    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
                      period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricAugmentedGraphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  constructor
  · intro hCritical
    rcases
        (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_graphResidualEulerSystem
          period hPeriod configuration data analysis chartData state).mp hCritical with
      ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
        hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hMetricEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hMetric
    exact ⟨
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hMetricEuler,
      hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField, hSpinC,
      hDiffeomorphism, hPotential, hAbelian⟩
  · intro hSystem
    rcases hSystem with
      ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
        hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hMetricEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hMetric
    apply
      (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_graphResidualEulerSystem
        period hPeriod configuration data analysis chartData state).mpr
    exact ⟨
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hMetricEuler,
      hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField, hSpinC,
      hDiffeomorphism, hPotential, hAbelian⟩

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_metricAugmentedGraphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphResidualEulerSystemAt
      period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricAugmentedGraphResidualEulerSystem
    period hPeriod configuration data analysis chartData state).mp hCritical

/-- Gate 257: the exact ten-block residual system now retains the authentic
diagonal diffeomorphism-BRST Hilbert coordinate in the metric equation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_augmented_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricAugmentedGraphResidualEulerSystem
    period hPeriod configuration data analysis chartData state

end MetricAugmentedResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
end JanusFormal
