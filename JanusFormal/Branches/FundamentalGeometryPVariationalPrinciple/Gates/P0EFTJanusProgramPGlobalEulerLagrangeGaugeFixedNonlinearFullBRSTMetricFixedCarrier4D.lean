import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingFiveRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphFaithfulness4D

/-!
# Fixed Hilbert carrier for the full-BRST metric coordinate

Pure metric tests have a state-independent closed carrier inside the authentic
diagonal diffeomorphism-BRST graph. They embed into it densely and injectively.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphFaithfulness4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

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

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section MetricCarrier

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

/-- State-independent authentic diagonal-BRST ambient space for metric tests. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphNormedSpaceDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphAddCommGroupDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphModuleDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphTopologicalSpaceDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientContinuousAdd :
    ContinuousAdd
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphContinuousAddDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientContinuousConstSMul :
    ContinuousConstSMul Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphContinuousConstSMulDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance (priority := 13000) metricFixedAmbientCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  diagonalGraphCompleteSpaceDiffeomorphismGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

/-- Fixed faithful diagonal-BRST coordinate of a pure metric test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseMap :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap
    period hPeriod configuration data

/-- Closed state-independent carrier of the metric graph coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseMap period
      hPeriod configuration data)).topologicalClosure

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure period hPeriod
    configuration data

@[implicit_reducible]
local instance (priority := 10001) metricFixedNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
      configuration data)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data))
    (diagonalGraphModuleDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data))
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure period hPeriod
      configuration data)

@[implicit_reducible]
local instance (priority := 10003) metricFixedPseudoMetricSpace :
    PseudoMetricSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedNormedAddCommGroup period hPeriod configuration data
    ).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) metricFixedUniformSpace :
    UniformSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedPseudoMetricSpace period hPeriod configuration data).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) metricFixedSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedNormedAddCommGroup period hPeriod configuration data
    ).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) metricFixedAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedNormedAddCommGroup period hPeriod configuration data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) metricFixedTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedUniformSpace period hPeriod configuration data).toTopologicalSpace

local instance (priority := 10001) metricFixedInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
      configuration data)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data)).toSeminormedAddCommGroup
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data))
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure period hPeriod
      configuration data)

@[implicit_reducible]
local instance (priority := 10001) metricFixedNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedInnerProductSpace period hPeriod configuration data).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) metricFixedModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) :=
  (metricFixedNormedSpace period hPeriod configuration data).toModule

/-- Canonical continuous inclusion of the fixed metric carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedInclusionCLM :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period hPeriod
        configuration data →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
        configuration data :=
  @Submodule.subtypeL Real inferInstance
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
      configuration data)
    (diagonalGraphTopologicalSpaceDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data))
    (diagonalGraphAddCommGroupDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data)).toAddCommMonoid
    (diagonalGraphModuleDiffeomorphismGhostResidual period hPeriod
      (BaseMetric period hPeriod configuration data))
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure period hPeriod
      configuration data)

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data) := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure
  exact isClosed_closure.completeSpace_coe

/-- Dense inclusion of pure metric tests into the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period
        hPeriod configuration data where
  toFun test :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseMap period
        hPeriod configuration data test,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseMap period
          hPeriod configuration data)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseMap period
            hPeriod configuration data) test)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar test := Subtype.ext (map_smul _ scalar test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
        period hPeriod configuration data) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseMap period hPeriod
      configuration data
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
            period hPeriod configuration data) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
            hPeriod configuration data)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
            period hPeriod configuration data test,
          ⟨test, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period
        hPeriod configuration data)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
        period hPeriod configuration data))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
        period hPeriod configuration data) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap_injective
      period hPeriod configuration data
  exact congrArg Subtype.val hEqual

/-- Gate 298: pure metric tests have a fixed complete closed carrier with a
dense injective embedding. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_fixed_carrier_gate :
    DenseRange
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data) ∧
      Function.Injective
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding_denseRange
      period hPeriod configuration data,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding_injective
      period hPeriod configuration data⟩

end MetricCarrier
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D
end JanusFormal
