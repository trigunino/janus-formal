import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricBaseRegularity4D

/-!
# Fixed-carrier formula for the metric graph residual

The canonical authentic base Riesz representative and a regular cross-block
remainder determine the authentic state-dependent graph residual by the exact
rank-one graph formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszFormula4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricBaseRegularity4D

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

attribute [local instance 10001]
  metricFixedNormedAddCommGroup
  metricFixedInnerProductSpace
  metricFixedNormedSpace
  metricFixedModule
attribute [local instance 10002]
  metricFixedSeminormedAddCommGroup
  metricFixedAddCommGroup
  metricFixedTopologicalSpace
attribute [local instance 10003]
  metricFixedPseudoMetricSpace
  metricFixedUniformSpace
variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev MetricTest :=
  GlobalMinimalPhysicalMetricTest period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section RegularFormula

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
    (measure := measure) configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev MetricBase :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
    configuration data

private abbrev MetricGraphAmbient :=
  WithLp 2 (MetricBase period hPeriod configuration data × Real)

@[implicit_reducible]
local instance (priority := 15000) metricFormulaAmbientNormedAddCommGroup :
    NormedAddCommGroup (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientNormedAddCommGroup period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15001) metricFormulaAmbientAddCommGroup :
    AddCommGroup (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientAddCommGroup period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15002) metricFormulaAmbientSeminormedAddCommGroup :
    SeminormedAddCommGroup (MetricBase period hPeriod configuration data) :=
  (metricFormulaAmbientNormedAddCommGroup period hPeriod configuration data
    ).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 15002) metricFormulaAmbientAddCommMonoid :
    AddCommMonoid (MetricBase period hPeriod configuration data) :=
  (metricFormulaAmbientAddCommGroup period hPeriod configuration data
    ).toAddCommMonoid

@[implicit_reducible]
local instance (priority := 15000) metricFormulaAmbientNormedSpace :
    NormedSpace Real (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientNormedSpace period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15000) metricFormulaAmbientModule :
    Module Real (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientModule period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15001) metricFormulaAmbientTopologicalSpace :
    TopologicalSpace (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientTopologicalSpace period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15000) metricFormulaAmbientInnerProductSpace :
    InnerProductSpace Real (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientInnerProductSpace period hPeriod configuration data

local instance (priority := 15000) metricFormulaAmbientCompleteSpace :
    CompleteSpace (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientCompleteSpace period hPeriod configuration data

local instance (priority := 15000) metricFormulaAmbientContinuousAdd :
    ContinuousAdd (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientContinuousAdd period hPeriod configuration data

local instance (priority := 15000) metricFormulaAmbientContinuousConstSMul :
    ContinuousConstSMul Real (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientContinuousConstSMul period hPeriod configuration data

private abbrev MetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert
    period hPeriod configuration data

private abbrev MetricClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedClosure
    period hPeriod configuration data

private abbrev MetricInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedInclusionCLM period hPeriod
    configuration data

private def metricFormulaCarrierInner
    (first second : MetricHilbert period hPeriod configuration data) : Real :=
  @inner Real (MetricBase period hPeriod configuration data)
    (metricFormulaAmbientInnerProductSpace period hPeriod configuration data
      ).toInner
    (first : MetricBase period hPeriod configuration data)
    (second : MetricBase period hPeriod configuration data)

private theorem metricFormulaCarrierInner_add_left
    (first second third : MetricHilbert period hPeriod configuration data) :
    metricFormulaCarrierInner period hPeriod configuration data
        (first + second) third =
      metricFormulaCarrierInner period hPeriod configuration data first third +
        metricFormulaCarrierInner period hPeriod configuration data second third := by
  unfold metricFormulaCarrierInner
  convert (@inner_add_left Real
    (MetricBase period hPeriod configuration data) inferInstance
    (metricFormulaAmbientSeminormedAddCommGroup period hPeriod configuration data)
    (metricFormulaAmbientInnerProductSpace period hPeriod configuration data)
    (first : MetricBase period hPeriod configuration data)
    (second : MetricBase period hPeriod configuration data)
    (third : MetricBase period hPeriod configuration data)) using 1; rfl

private theorem metricFormulaCarrierInner_sub_left
    (first second third : MetricHilbert period hPeriod configuration data) :
    metricFormulaCarrierInner period hPeriod configuration data
        (first - second) third =
      metricFormulaCarrierInner period hPeriod configuration data first third -
        metricFormulaCarrierInner period hPeriod configuration data second third := by
  unfold metricFormulaCarrierInner
  convert (@inner_sub_left Real
    (MetricBase period hPeriod configuration data) inferInstance
    (metricFormulaAmbientSeminormedAddCommGroup period hPeriod configuration data)
    (metricFormulaAmbientInnerProductSpace period hPeriod configuration data)
    (first : MetricBase period hPeriod configuration data)
    (second : MetricBase period hPeriod configuration data)
    (third : MetricBase period hPeriod configuration data)) using 1; rfl

private theorem metricFormulaCarrierInner_smul_left
    (scalar : Real)
    (first second : MetricHilbert period hPeriod configuration data) :
    metricFormulaCarrierInner period hPeriod configuration data
        (scalar • first) second =
      scalar * metricFormulaCarrierInner period hPeriod configuration data
        first second := by
  unfold metricFormulaCarrierInner
  convert (@real_inner_smul_left
    (MetricBase period hPeriod configuration data)
    (metricFormulaAmbientSeminormedAddCommGroup period hPeriod configuration data)
    (metricFormulaAmbientInnerProductSpace period hPeriod configuration data)
    (first : MetricBase period hPeriod configuration data)
    (second : MetricBase period hPeriod configuration data) scalar) using 1; rfl

private theorem metricFormulaCarrierInner_eq_fixedInner
    (first second : MetricHilbert period hPeriod configuration data) :
    metricFormulaCarrierInner period hPeriod configuration data first second =
      @inner Real (MetricHilbert period hPeriod configuration data)
        (metricFixedInnerProductSpace period hPeriod configuration data).toInner
        first second := by
  rfl

private abbrev GraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
    period hPeriod configuration data analysis chartData state

private abbrev StateGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (GraphData period hPeriod configuration data analysis chartData state
    ).toStateDependent period hPeriod
      (BaseMetric period hPeriod configuration data) (MetricTest period hPeriod)

private abbrev GraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphHilbert
    period hPeriod configuration data analysis chartData state

local instance metricHilbertCompleteSpace :
    CompleteSpace
      (MetricHilbert period hPeriod configuration data) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedCompleteSpace
    period hPeriod configuration data

local instance graphHilbertCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (GraphHilbert period hPeriod configuration data analysis chartData state) :=
  stateDependentAugmentedGraphCompleteSpace
    (StateGraphData period hPeriod configuration data analysis chartData state)

/-- Continuous graph of the regular cross-block remainder on the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricHilbert period hPeriod configuration data →L[Real]
      MetricGraphAmbient period hPeriod configuration data :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (MetricBase period hPeriod configuration data) Real
    ).symm.toContinuousLinearMap.comp
      ((MetricInclusion period hPeriod configuration data).prod
        (regularity.covector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : MetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data test) =
      stateDependentAugmentedGraphLinearMap
        (StateGraphData period hPeriod configuration data analysis chartData state)
        test := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · change regularity.covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data test) =
      (GraphData period hPeriod configuration data analysis chartData state
        ).remainder test
    exact regularity.represents state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : MetricHilbert period hPeriod configuration data) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph
        period hPeriod configuration data analysis chartData regularity state value ∈
      stateDependentAugmentedGraphSubmodule
        (StateGraphData period hPeriod configuration data analysis chartData state) := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph
      period hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data
  let raw := stateDependentAugmentedGraphLinearMap
    (StateGraphData period hPeriod configuration data analysis chartData state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding_denseRange
      period hPeriod configuration data
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (MetricGraphAmbient period hPeriod configuration data))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨test, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw test

/-- Lift of the fixed regular graph into the authentic completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricHilbert period hPeriod configuration data →L[Real]
      GraphHilbert period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph
      period hPeriod configuration data analysis chartData regularity state
    ).codRestrict
      (stateDependentAugmentedGraphSubmodule
        (StateGraphData period hPeriod configuration data analysis chartData state))
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph_mem
        period hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : MetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data test) =
      stateDependentAugmentedGraphEmbedding
        (StateGraphData period hPeriod configuration data analysis chartData state)
        test := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (StateGraphData period hPeriod configuration data analysis chartData state)).mono
  rintro result ⟨test, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data test,
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state test⟩

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularTotalRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricHilbert period hPeriod configuration data :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state +
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  inner Real remainder total / (1 + ‖remainder‖ ^ 2)

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularCarrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricHilbert period hPeriod configuration data :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  total - scale • remainder

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GraphHilbert period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricGraphAmbient period hPeriod configuration data :=
  WithLp.toLp 2
    (((globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state :
          MetricHilbert period hPeriod configuration data) :
        MetricBase period hPeriod configuration data),
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state)

private theorem regularity_covector_carrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    regularity.covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state := by
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  have hDen : 1 + ‖remainder‖ ^ 2 ≠ 0 := by positivity
  change regularity.covector state (total - scale • remainder) = scale
  rw [map_sub, map_smul, smul_eq_mul]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_pairing]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_pairing]
  rw [real_inner_self_eq_norm_sq]
  dsimp only [scale]
  field_simp [hDen]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : MetricHilbert period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      (GraphData period hPeriod configuration data analysis chartData state
        ).baseCovector
          (MetricInclusion period hPeriod configuration data test) +
        regularity.covector state test := by
  let base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total := base + remainder
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  let carrierValue := total - scale • remainder
  have hCarrierValue := regularity_covector_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  change regularity.covector state carrierValue = scale at hCarrierValue
  change inner Real
      (WithLp.toLp 2
        (((carrierValue : MetricHilbert period hPeriod configuration data) :
          MetricBase period hPeriod configuration data),
          regularity.covector state carrierValue))
      (WithLp.toLp 2
        (((test : MetricHilbert period hPeriod configuration data) :
          MetricBase period hPeriod configuration data),
          regularity.covector state test)) = _
  rw [WithLp.prod_inner_apply]
  simp only [Real.inner_apply]
  change metricFormulaCarrierInner period hPeriod configuration data
        carrierValue test +
      regularity.covector state carrierValue * regularity.covector state test = _
  rw [hCarrierValue]
  dsimp only [carrierValue, total]
  rw [metricFormulaCarrierInner_sub_left,
    metricFormulaCarrierInner_smul_left,
    metricFormulaCarrierInner_add_left]
  rw [metricFormulaCarrierInner_eq_fixedInner]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative_pairing]
  rw [metricFormulaCarrierInner_eq_fixedInner]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_pairing]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact regularity_covector_carrierValue period hPeriod configuration data
      analysis chartData regularity state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  apply
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding_denseRange
      period hPeriod configuration data analysis chartData regularity state
      ).eq_of_inner_left Real
  intro test
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      stateDependentAugmentedGraphCovector
        (StateGraphData period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) := by
        exact stateDependentAugmentedGraphRieszResidual_pairing _ _
    _ = (GraphData period hPeriod configuration data analysis chartData state
          ).baseCovector
            (MetricInclusion period hPeriod configuration data test) +
          regularity.covector state test := by
        rfl
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
          test).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-- Gate 301: the authentic metric graph residual equals its explicit
fixed-carrier rank-one formula. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_regular_graph_riesz_formula_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual_eq_regularFormula
    period hPeriod configuration data analysis chartData regularity state

end RegularFormula
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszFormula4D
end JanusFormal
