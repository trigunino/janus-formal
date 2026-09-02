import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotBaseRegularity4D

/-!
# Fixed-carrier formulas for the three LL graph residuals

The smooth restricted base and remainder representatives determine each
authentic LL augmented-graph residual by the exact rank-one graph formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRegularGraphRieszFormula4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotBaseRegularity4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  llAuxMetricFixedNormedAddCommGroup
  llAuxMetricFixedInnerProductSpace
  llAuxMetricFixedNormedSpace
  llAuxMetricFixedModule
  llMeasureFixedNormedAddCommGroup
  llMeasureFixedInnerProductSpace
  llMeasureFixedNormedSpace
  llMeasureFixedModule
  llFieldFixedNormedAddCommGroup
  llFieldFixedInnerProductSpace
  llFieldFixedNormedSpace
  llFieldFixedModule
attribute [local instance 10002]
  llAuxMetricFixedSeminormedAddCommGroup
  llAuxMetricFixedAddCommGroup
  llAuxMetricFixedTopologicalSpace
  llMeasureFixedSeminormedAddCommGroup
  llMeasureFixedAddCommGroup
  llMeasureFixedTopologicalSpace
  llFieldFixedSeminormedAddCommGroup
  llFieldFixedAddCommGroup
  llFieldFixedTopologicalSpace
attribute [local instance 10003]
  llAuxMetricFixedPseudoMetricSpace
  llAuxMetricFixedUniformSpace
  llMeasureFixedPseudoMetricSpace
  llMeasureFixedUniformSpace
  llFieldFixedPseudoMetricSpace
  llFieldFixedUniformSpace

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

private abbrev LLCommonAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
    hPeriod configuration data analysis

private abbrev LLGraphAmbient :=
  WithLp 2 (LLCommonAmbient period hPeriod configuration data analysis × Real)

private abbrev LLAuxMetricTest :=
  GlobalMinimalPhysicalLLAuxMetricTest period hPeriod

private abbrev LLMeasureTest :=
  GlobalMinimalPhysicalLLMeasureTest period hPeriod

private abbrev LLFieldTest :=
  GlobalMinimalPhysicalLLFieldTest period hPeriod

private abbrev LLAuxMetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLMeasureHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLFieldHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period hPeriod
    configuration data analysis chartData

private abbrev LLAuxMetricInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedInclusionCLM
    period hPeriod configuration data analysis chartData

private abbrev LLMeasureInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedInclusionCLM period
    hPeriod configuration data analysis chartData

private abbrev LLFieldInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedInclusionCLM period
    hPeriod configuration data analysis chartData

private abbrev LLAuxMetricGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
    period hPeriod configuration data analysis chartData state

private abbrev LLMeasureGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
    period hPeriod configuration data analysis chartData state

private abbrev LLFieldGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData period
    hPeriod configuration data analysis chartData state

private abbrev LLAuxMetricGraphSubmodule
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Submodule Real
      (LLGraphAmbient period hPeriod configuration data analysis) :=
  @stateDependentAugmentedGraphSubmodule
    (LLAuxMetricTest period hPeriod)
    (LLCommonAmbient period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    (LLAuxMetricGraphData period hPeriod configuration data analysis chartData
      state)

private abbrev LLMeasureGraphSubmodule
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Submodule Real
      (LLGraphAmbient period hPeriod configuration data analysis) :=
  @stateDependentAugmentedGraphSubmodule
    (LLMeasureTest period hPeriod)
    (LLCommonAmbient period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    (LLMeasureGraphData period hPeriod configuration data analysis chartData
      state)

private abbrev LLFieldGraphSubmodule
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Submodule Real
      (LLGraphAmbient period hPeriod configuration data analysis) :=
  @stateDependentAugmentedGraphSubmodule
    (LLFieldTest period hPeriod)
    (LLCommonAmbient period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    (LLFieldGraphData period hPeriod configuration data analysis chartData state)

private abbrev LLAuxMetricGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphHilbert
    period hPeriod configuration data analysis chartData state

private abbrev LLMeasureGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphHilbert
    period hPeriod configuration data analysis chartData state

private abbrev LLFieldGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphHilbert
    period hPeriod configuration data analysis chartData state

@[implicit_reducible]
local instance (priority := 15000) llCommonAmbientInnerProductSpace :
    InnerProductSpace Real
      (LLCommonAmbient period hPeriod configuration data analysis) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
    period hPeriod configuration data analysis

local instance (priority := 15000) llCommonAmbientCompleteSpace :
    CompleteSpace
      (LLCommonAmbient period hPeriod configuration data analysis) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
    period hPeriod configuration data analysis

@[implicit_reducible]
local instance (priority := 15000) llGraphAmbientInnerProductSpace :
    InnerProductSpace Real
      (LLGraphAmbient period hPeriod configuration data analysis) :=
  @WithLp.instProdInnerProductSpace Real
    (LLCommonAmbient period hPeriod configuration data analysis) Real
    inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    inferInstance inferInstance

local instance (priority := 15000) llAuxMetricHilbertCompleteSpace :
    CompleteSpace
      (LLAuxMetricHilbert period hPeriod configuration data analysis
        chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedCompleteSpace
    period hPeriod configuration data analysis chartData

local instance (priority := 15000) llMeasureHilbertCompleteSpace :
    CompleteSpace
      (LLMeasureHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedCompleteSpace period
    hPeriod configuration data analysis chartData

local instance (priority := 15000) llFieldHilbertCompleteSpace :
    CompleteSpace
      (LLFieldHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedCompleteSpace period
    hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 15000) llAuxMetricGraphHilbertInnerProductSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    InnerProductSpace Real
      (LLAuxMetricGraphHilbert period hPeriod configuration data analysis
        chartData state) :=
  @Submodule.innerProductSpace Real
    (LLGraphAmbient period hPeriod configuration data analysis)
    inferInstance inferInstance
    (llGraphAmbientInnerProductSpace period hPeriod configuration data analysis)
    (LLAuxMetricGraphSubmodule period hPeriod configuration data analysis
      chartData state)

@[implicit_reducible]
local instance (priority := 15000) llMeasureGraphHilbertInnerProductSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    InnerProductSpace Real
      (LLMeasureGraphHilbert period hPeriod configuration data analysis
        chartData state) :=
  @Submodule.innerProductSpace Real
    (LLGraphAmbient period hPeriod configuration data analysis)
    inferInstance inferInstance
    (llGraphAmbientInnerProductSpace period hPeriod configuration data analysis)
    (LLMeasureGraphSubmodule period hPeriod configuration data analysis chartData
      state)

@[implicit_reducible]
local instance (priority := 15000) llFieldGraphHilbertInnerProductSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    InnerProductSpace Real
      (LLFieldGraphHilbert period hPeriod configuration data analysis chartData
        state) :=
  @Submodule.innerProductSpace Real
    (LLGraphAmbient period hPeriod configuration data analysis)
    inferInstance inferInstance
    (llGraphAmbientInnerProductSpace period hPeriod configuration data analysis)
    (LLFieldGraphSubmodule period hPeriod configuration data analysis chartData
      state)

private theorem llAuxMetricGraphAmbient_inner_apply
    (first second : LLAuxMetricHilbert period hPeriod configuration data analysis
      chartData) (firstScalar secondScalar : Real) :
    @inner Real (LLGraphAmbient period hPeriod configuration data analysis)
        (llGraphAmbientInnerProductSpace period hPeriod configuration data
          analysis).toInner
        (WithLp.toLp 2 (((first : LLAuxMetricHilbert period hPeriod
          configuration data analysis chartData) :
            LLCommonAmbient period hPeriod configuration data analysis),
          firstScalar))
        (WithLp.toLp 2 (((second : LLAuxMetricHilbert period hPeriod
          configuration data analysis chartData) :
            LLCommonAmbient period hPeriod configuration data analysis),
          secondScalar)) =
      @inner Real
          (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
          (llAuxMetricFixedInnerProductSpace period hPeriod configuration data
            analysis chartData).toInner first second +
        firstScalar * secondScalar := by
  unfold llGraphAmbientInnerProductSpace
  rw [@WithLp.prod_inner_apply Real
    (LLCommonAmbient period hPeriod configuration data analysis) Real
    inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    inferInstance inferInstance _ _]
  simp only [Real.inner_apply]
  rfl

private theorem llMeasureGraphAmbient_inner_apply
    (first second : LLMeasureHilbert period hPeriod configuration data analysis
      chartData) (firstScalar secondScalar : Real) :
    @inner Real (LLGraphAmbient period hPeriod configuration data analysis)
        (llGraphAmbientInnerProductSpace period hPeriod configuration data
          analysis).toInner
        (WithLp.toLp 2 (((first : LLMeasureHilbert period hPeriod configuration
          data analysis chartData) :
            LLCommonAmbient period hPeriod configuration data analysis),
          firstScalar))
        (WithLp.toLp 2 (((second : LLMeasureHilbert period hPeriod configuration
          data analysis chartData) :
            LLCommonAmbient period hPeriod configuration data analysis),
          secondScalar)) =
      @inner Real
          (LLMeasureHilbert period hPeriod configuration data analysis chartData)
          (llMeasureFixedInnerProductSpace period hPeriod configuration data
            analysis chartData).toInner first second +
        firstScalar * secondScalar := by
  unfold llGraphAmbientInnerProductSpace
  rw [@WithLp.prod_inner_apply Real
    (LLCommonAmbient period hPeriod configuration data analysis) Real
    inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    inferInstance inferInstance _ _]
  simp only [Real.inner_apply]
  rfl

private theorem llFieldGraphAmbient_inner_apply
    (first second : LLFieldHilbert period hPeriod configuration data analysis
      chartData) (firstScalar secondScalar : Real) :
    @inner Real (LLGraphAmbient period hPeriod configuration data analysis)
        (llGraphAmbientInnerProductSpace period hPeriod configuration data
          analysis).toInner
        (WithLp.toLp 2 (((first : LLFieldHilbert period hPeriod configuration
          data analysis chartData) :
            LLCommonAmbient period hPeriod configuration data analysis),
          firstScalar))
        (WithLp.toLp 2 (((second : LLFieldHilbert period hPeriod configuration
          data analysis chartData) :
            LLCommonAmbient period hPeriod configuration data analysis),
          secondScalar)) =
      @inner Real
          (LLFieldHilbert period hPeriod configuration data analysis chartData)
          (llFieldFixedInnerProductSpace period hPeriod configuration data
            analysis chartData).toInner first second +
        firstScalar * secondScalar := by
  unfold llGraphAmbientInnerProductSpace
  rw [@WithLp.prod_inner_apply Real
    (LLCommonAmbient period hPeriod configuration data analysis) Real
    inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    inferInstance inferInstance _ _]
  simp only [Real.inner_apply]
  rfl

local instance (priority := 15000) llAuxMetricGraphHilbertCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (LLAuxMetricGraphHilbert period hPeriod configuration data analysis
        chartData state) :=
  stateDependentAugmentedGraphCompleteSpace
    (LLAuxMetricGraphData period hPeriod configuration data analysis chartData
      state)

local instance (priority := 15000) llMeasureGraphHilbertCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (LLMeasureGraphHilbert period hPeriod configuration data analysis
        chartData state) :=
  stateDependentAugmentedGraphCompleteSpace
    (LLMeasureGraphData period hPeriod configuration data analysis chartData
      state)

local instance (priority := 15000) llFieldGraphHilbertCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (LLFieldGraphHilbert period hPeriod configuration data analysis chartData
        state) :=
  stateDependentAugmentedGraphCompleteSpace
    (LLFieldGraphData period hPeriod configuration data analysis chartData
      state)

/-! ## Auxiliary-metric slot -/

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLAuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
      LLGraphAmbient period hPeriod configuration data analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (LLCommonAmbient period hPeriod configuration data analysis) Real
    ).symm.toContinuousLinearMap.comp
      ((LLAuxMetricInclusion period hPeriod configuration data analysis
        chartData).prod (regularity.auxMetricCovector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLAuxMetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph period
        hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphLinearMap
        (LLAuxMetricGraphData period hPeriod configuration data analysis
          chartData state) test := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact regularity.auxMetricRepresents state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : LLAuxMetricHilbert period hPeriod configuration data analysis
      chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph period
        hPeriod configuration data analysis chartData regularity state value ∈
      LLAuxMetricGraphSubmodule period hPeriod configuration data analysis
        chartData state := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph period
      hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
      period hPeriod configuration data analysis chartData
  let raw := stateDependentAugmentedGraphLinearMap
    (LLAuxMetricGraphData period hPeriod configuration data analysis chartData
      state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (LLGraphAmbient period hPeriod configuration data analysis))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨test, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw test

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLAuxMetricHilbert period hPeriod configuration data analysis chartData →L[Real]
      LLAuxMetricGraphHilbert period hPeriod configuration data analysis
        chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph period
      hPeriod configuration data analysis chartData regularity state).codRestrict
    (LLAuxMetricGraphSubmodule period hPeriod configuration data analysis
      chartData state)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph_mem
      period hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLAuxMetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphEmbedding
        (LLAuxMetricGraphData period hPeriod configuration data analysis
          chartData state) test := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (LLAuxMetricGraphData period hPeriod configuration data analysis chartData
      state)).mono
  rintro result ⟨test, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
        period hPeriod configuration data analysis chartData test,
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state
          test⟩

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularTotalRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLAuxMetricHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state +
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  inner Real remainder total / (1 + ‖remainder‖ ^ 2)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularCarrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLAuxMetricHilbert period hPeriod configuration data analysis chartData :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  total - scale • remainder

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLAuxMetricGraphHilbert period hPeriod configuration data analysis
      chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLGraphAmbient period hPeriod configuration data analysis :=
  WithLp.toLp 2
    (((globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state :
          LLAuxMetricHilbert period hPeriod configuration data analysis
            chartData) :
        LLCommonAmbient period hPeriod configuration data analysis),
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state)

private theorem llAuxMetricRegularity_covector_carrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    regularity.auxMetricCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state := by
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  have hDen : 1 + ‖remainder‖ ^ 2 ≠ 0 := by positivity
  change regularity.auxMetricCovector state (total - scale • remainder) = scale
  rw [map_sub, map_smul, smul_eq_mul]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_pairing]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_pairing]
  rw [real_inner_self_eq_norm_sq]
  dsimp only [scale]
  field_simp [hDen]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLAuxMetricHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      (LLAuxMetricGraphData period hPeriod configuration data analysis chartData
        state).baseCovector
          (LLAuxMetricInclusion period hPeriod configuration data analysis
            chartData test) + regularity.auxMetricCovector state test := by
  let base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total := base + remainder
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  let carrierValue := total - scale • remainder
  have hCarrierValue := llAuxMetricRegularity_covector_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  change regularity.auxMetricCovector state carrierValue = scale at hCarrierValue
  change inner Real
      (WithLp.toLp 2
        (((carrierValue : LLAuxMetricHilbert period hPeriod configuration data
            analysis chartData) :
          LLCommonAmbient period hPeriod configuration data analysis),
          regularity.auxMetricCovector state carrierValue))
      (WithLp.toLp 2
        (((test : LLAuxMetricHilbert period hPeriod configuration data analysis
            chartData) :
          LLCommonAmbient period hPeriod configuration data analysis),
          regularity.auxMetricCovector state test)) = _
  rw [llAuxMetricGraphAmbient_inner_apply]
  calc
    _ = inner Real carrierValue test +
        scale * regularity.auxMetricCovector state test := by
      exact congrArg (fun value : Real =>
        inner Real carrierValue test +
          value * regularity.auxMetricCovector state test) hCarrierValue
    _ = _ := by
      have hSub : inner Real (total - scale • remainder) test =
          inner Real total test - inner Real (scale • remainder) test :=
        @inner_sub_left Real
          (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
          inferInstance
          (llAuxMetricFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llAuxMetricFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          total (scale • remainder) test
      have hSmul : inner Real (scale • remainder) test =
          scale * inner Real remainder test :=
        @real_inner_smul_left
          (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
          (llAuxMetricFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llAuxMetricFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          remainder test scale
      have hTotal : inner Real total test =
          inner Real base test + inner Real remainder test := by
        dsimp only [total]
        exact @inner_add_left Real
          (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
          inferInstance
          (llAuxMetricFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llAuxMetricFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          base remainder test
      have hCarrierInner : inner Real carrierValue test =
          (inner Real base test + inner Real remainder test) -
            scale * inner Real remainder test := by
        dsimp only [carrierValue]
        calc
          _ = inner Real total test - inner Real (scale • remainder) test := hSub
          _ = inner Real total test - scale * inner Real remainder test :=
            congrArg (fun value : Real => inner Real total test - value) hSmul
          _ = (inner Real base test + inner Real remainder test) -
              scale * inner Real remainder test :=
            congrArg (fun value : Real =>
              value - scale * inner Real remainder test) hTotal
      have hBase : inner Real base test =
          (LLAuxMetricGraphData period hPeriod configuration data analysis
            chartData state).baseCovector
            (LLAuxMetricInclusion period hPeriod configuration data analysis
              chartData test) := by
        dsimp only [base]
        exact
          globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative_pairing
            period hPeriod configuration data analysis chartData state test
      have hRemainder : inner Real remainder test =
          regularity.auxMetricCovector state test := by
        dsimp only [remainder]
        exact
          globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_pairing
            period hPeriod configuration data analysis chartData regularity state
              test
      have hPairSum := congrArg₂ (fun first second : Real => first + second)
        hBase hRemainder
      have hScaled := congrArg (fun value : Real => scale * value) hRemainder
      have hDifference := congrArg₂ (fun first second : Real => first - second)
        hPairSum hScaled
      calc
        _ = ((inner Real base test + inner Real remainder test) -
              scale * inner Real remainder test) +
            scale * regularity.auxMetricCovector state test :=
          congrArg (fun value : Real =>
            value + scale * regularity.auxMetricCovector state test) hCarrierInner
        _ = (((LLAuxMetricGraphData period hPeriod configuration data analysis
                chartData state).baseCovector
                (LLAuxMetricInclusion period hPeriod configuration data analysis
                  chartData test) + regularity.auxMetricCovector state test) -
              scale * regularity.auxMetricCovector state test) +
            scale * regularity.auxMetricCovector state test :=
          congrArg (fun value : Real =>
            value + scale * regularity.auxMetricCovector state test) hDifference
        _ = _ := by ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact llAuxMetricRegularity_covector_carrierValue period hPeriod
      configuration data analysis chartData regularity state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  letI : InnerProductSpace Real
      (LLAuxMetricGraphHilbert period hPeriod configuration data analysis
        chartData state) :=
    llAuxMetricGraphHilbertInnerProductSpace period hPeriod configuration data
      analysis chartData state
  letI : CompleteSpace
      (LLAuxMetricGraphHilbert period hPeriod configuration data analysis
        chartData state) :=
    llAuxMetricGraphHilbertCompleteSpace period hPeriod configuration data
      analysis chartData state
  refine @DenseRange.eq_of_inner_left
    (LLAuxMetricGraphHilbert period hPeriod configuration data analysis chartData
      state)
    (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
    Real inferInstance inferInstance
    (llAuxMetricGraphHilbertInnerProductSpace period hPeriod configuration data
      analysis chartData state)
    _ _ _
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding_denseRange
      period hPeriod configuration data analysis chartData regularity state) ?_
  intro test
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      stateDependentAugmentedGraphCovector
        (LLAuxMetricGraphData period hPeriod configuration data analysis
          chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) := by
        exact stateDependentAugmentedGraphRieszResidual_pairing _ _
    _ = (LLAuxMetricGraphData period hPeriod configuration data analysis
          chartData state).baseCovector
            (LLAuxMetricInclusion period hPeriod configuration data analysis
              chartData test) + regularity.auxMetricCovector state test := by
        rfl
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
          test).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-! ## Measure slot -/

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLMeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
      LLGraphAmbient period hPeriod configuration data analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (LLCommonAmbient period hPeriod configuration data analysis) Real
    ).symm.toContinuousLinearMap.comp
      ((LLMeasureInclusion period hPeriod configuration data analysis
        chartData).prod (regularity.measureCovector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLMeasureTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph period
        hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphLinearMap
        (LLMeasureGraphData period hPeriod configuration data analysis
          chartData state) test := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact regularity.measureRepresents state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : LLMeasureHilbert period hPeriod configuration data analysis
      chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph period
        hPeriod configuration data analysis chartData regularity state value ∈
      LLMeasureGraphSubmodule period hPeriod configuration data analysis
        chartData state := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph period
      hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
      period hPeriod configuration data analysis chartData
  let raw := stateDependentAugmentedGraphLinearMap
    (LLMeasureGraphData period hPeriod configuration data analysis chartData
      state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (LLGraphAmbient period hPeriod configuration data analysis))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨test, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw test

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLMeasureHilbert period hPeriod configuration data analysis chartData →L[Real]
      LLMeasureGraphHilbert period hPeriod configuration data analysis chartData
        state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph period
      hPeriod configuration data analysis chartData regularity state).codRestrict
    (LLMeasureGraphSubmodule period hPeriod configuration data analysis chartData
      state)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph_mem period
      hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLMeasureTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphEmbedding
        (LLMeasureGraphData period hPeriod configuration data analysis
          chartData state) test := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (LLMeasureGraphData period hPeriod configuration data analysis chartData
      state)).mono
  rintro result ⟨test, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
        period hPeriod configuration data analysis chartData test,
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state
          test⟩

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularTotalRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLMeasureHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state +
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  inner Real remainder total / (1 + ‖remainder‖ ^ 2)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularCarrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLMeasureHilbert period hPeriod configuration data analysis chartData :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  total - scale • remainder

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLMeasureGraphHilbert period hPeriod configuration data analysis chartData
      state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLGraphAmbient period hPeriod configuration data analysis :=
  WithLp.toLp 2
    (((globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state :
          LLMeasureHilbert period hPeriod configuration data analysis
            chartData) :
        LLCommonAmbient period hPeriod configuration data analysis),
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state)

private theorem llMeasureRegularity_covector_carrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    regularity.measureCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state := by
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  have hDen : 1 + ‖remainder‖ ^ 2 ≠ 0 := by positivity
  change regularity.measureCovector state (total - scale • remainder) = scale
  rw [map_sub, map_smul, smul_eq_mul]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_pairing]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_pairing]
  rw [real_inner_self_eq_norm_sq]
  dsimp only [scale]
  field_simp [hDen]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLMeasureHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      (LLMeasureGraphData period hPeriod configuration data analysis chartData
        state).baseCovector
          (LLMeasureInclusion period hPeriod configuration data analysis
            chartData test) + regularity.measureCovector state test := by
  let base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total := base + remainder
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  let carrierValue := total - scale • remainder
  have hCarrierValue := llMeasureRegularity_covector_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  change regularity.measureCovector state carrierValue = scale at hCarrierValue
  change inner Real
      (WithLp.toLp 2
        (((carrierValue : LLMeasureHilbert period hPeriod configuration data
            analysis chartData) :
          LLCommonAmbient period hPeriod configuration data analysis),
          regularity.measureCovector state carrierValue))
      (WithLp.toLp 2
        (((test : LLMeasureHilbert period hPeriod configuration data analysis
            chartData) :
          LLCommonAmbient period hPeriod configuration data analysis),
          regularity.measureCovector state test)) = _
  rw [llMeasureGraphAmbient_inner_apply]
  calc
    _ = inner Real carrierValue test +
        scale * regularity.measureCovector state test := by
      exact congrArg (fun value : Real =>
        inner Real carrierValue test +
          value * regularity.measureCovector state test) hCarrierValue
    _ = _ := by
      have hSub : inner Real (total - scale • remainder) test =
          inner Real total test - inner Real (scale • remainder) test :=
        @inner_sub_left Real
          (LLMeasureHilbert period hPeriod configuration data analysis chartData)
          inferInstance
          (llMeasureFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llMeasureFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          total (scale • remainder) test
      have hSmul : inner Real (scale • remainder) test =
          scale * inner Real remainder test :=
        @real_inner_smul_left
          (LLMeasureHilbert period hPeriod configuration data analysis chartData)
          (llMeasureFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llMeasureFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          remainder test scale
      have hTotal : inner Real total test =
          inner Real base test + inner Real remainder test := by
        dsimp only [total]
        exact @inner_add_left Real
          (LLMeasureHilbert period hPeriod configuration data analysis chartData)
          inferInstance
          (llMeasureFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llMeasureFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          base remainder test
      have hCarrierInner : inner Real carrierValue test =
          (inner Real base test + inner Real remainder test) -
            scale * inner Real remainder test := by
        dsimp only [carrierValue]
        calc
          _ = inner Real total test - inner Real (scale • remainder) test := hSub
          _ = inner Real total test - scale * inner Real remainder test :=
            congrArg (fun value : Real => inner Real total test - value) hSmul
          _ = (inner Real base test + inner Real remainder test) -
              scale * inner Real remainder test :=
            congrArg (fun value : Real =>
              value - scale * inner Real remainder test) hTotal
      have hBase : inner Real base test =
          (LLMeasureGraphData period hPeriod configuration data analysis
            chartData state).baseCovector
            (LLMeasureInclusion period hPeriod configuration data analysis
              chartData test) := by
        dsimp only [base]
        exact
          globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative_pairing
            period hPeriod configuration data analysis chartData state test
      have hRemainder : inner Real remainder test =
          regularity.measureCovector state test := by
        dsimp only [remainder]
        exact
          globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_pairing
            period hPeriod configuration data analysis chartData regularity state
              test
      have hPairSum := congrArg₂ (fun first second : Real => first + second)
        hBase hRemainder
      have hScaled := congrArg (fun value : Real => scale * value) hRemainder
      have hDifference := congrArg₂ (fun first second : Real => first - second)
        hPairSum hScaled
      calc
        _ = ((inner Real base test + inner Real remainder test) -
              scale * inner Real remainder test) +
            scale * regularity.measureCovector state test :=
          congrArg (fun value : Real =>
            value + scale * regularity.measureCovector state test) hCarrierInner
        _ = (((LLMeasureGraphData period hPeriod configuration data analysis
                chartData state).baseCovector
                (LLMeasureInclusion period hPeriod configuration data analysis
                  chartData test) + regularity.measureCovector state test) -
              scale * regularity.measureCovector state test) +
            scale * regularity.measureCovector state test :=
          congrArg (fun value : Real =>
            value + scale * regularity.measureCovector state test) hDifference
        _ = _ := by ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact llMeasureRegularity_covector_carrierValue period hPeriod
      configuration data analysis chartData regularity state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  letI : InnerProductSpace Real
      (LLMeasureGraphHilbert period hPeriod configuration data analysis chartData
        state) :=
    llMeasureGraphHilbertInnerProductSpace period hPeriod configuration data
      analysis chartData state
  letI : CompleteSpace
      (LLMeasureGraphHilbert period hPeriod configuration data analysis chartData
        state) :=
    llMeasureGraphHilbertCompleteSpace period hPeriod configuration data analysis
      chartData state
  refine @DenseRange.eq_of_inner_left
    (LLMeasureGraphHilbert period hPeriod configuration data analysis chartData
      state)
    (LLMeasureHilbert period hPeriod configuration data analysis chartData)
    Real inferInstance inferInstance
    (llMeasureGraphHilbertInnerProductSpace period hPeriod configuration data
      analysis chartData state)
    _ _ _
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding_denseRange
      period hPeriod configuration data analysis chartData regularity state) ?_
  intro test
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      stateDependentAugmentedGraphCovector
        (LLMeasureGraphData period hPeriod configuration data analysis chartData
          state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) := by
        exact stateDependentAugmentedGraphRieszResidual_pairing _ _
    _ = (LLMeasureGraphData period hPeriod configuration data analysis
          chartData state).baseCovector
            (LLMeasureInclusion period hPeriod configuration data analysis
              chartData test) + regularity.measureCovector state test := by
        rfl
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
          test).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-! ## Field slot -/

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLFieldHilbert period hPeriod configuration data analysis chartData →L[Real]
      LLGraphAmbient period hPeriod configuration data analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (LLCommonAmbient period hPeriod configuration data analysis) Real
    ).symm.toContinuousLinearMap.comp
      ((LLFieldInclusion period hPeriod configuration data analysis
        chartData).prod (regularity.fieldCovector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLFieldTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph period
        hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphLinearMap
        (LLFieldGraphData period hPeriod configuration data analysis chartData
          state) test := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact regularity.fieldRepresents state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : LLFieldHilbert period hPeriod configuration data analysis
      chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph period
        hPeriod configuration data analysis chartData regularity state value ∈
      LLFieldGraphSubmodule period hPeriod configuration data analysis chartData
        state := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph period
      hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
      period hPeriod configuration data analysis chartData
  let raw := stateDependentAugmentedGraphLinearMap
    (LLFieldGraphData period hPeriod configuration data analysis chartData
      state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (LLGraphAmbient period hPeriod configuration data analysis))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨test, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw test

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLFieldHilbert period hPeriod configuration data analysis chartData →L[Real]
      LLFieldGraphHilbert period hPeriod configuration data analysis chartData
        state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph period hPeriod
      configuration data analysis chartData regularity state).codRestrict
    (LLFieldGraphSubmodule period hPeriod configuration data analysis chartData
      state)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph_mem period
      hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLFieldTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphEmbedding
        (LLFieldGraphData period hPeriod configuration data analysis chartData
          state) test := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (LLFieldGraphData period hPeriod configuration data analysis chartData
      state)).mono
  rintro result ⟨test, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
        period hPeriod configuration data analysis chartData test,
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state
          test⟩

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularTotalRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLFieldHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state +
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  inner Real remainder total / (1 + ‖remainder‖ ^ 2)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularCarrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLFieldHilbert period hPeriod configuration data analysis chartData :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularRieszScale period
      hPeriod configuration data analysis chartData regularity state
  total - scale • remainder

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLFieldGraphHilbert period hPeriod configuration data analysis chartData
      state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLGraphAmbient period hPeriod configuration data analysis :=
  WithLp.toLp 2
    (((globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state :
          LLFieldHilbert period hPeriod configuration data analysis chartData) :
        LLCommonAmbient period hPeriod configuration data analysis),
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularRieszScale period
        hPeriod configuration data analysis chartData regularity state)

private theorem llFieldRegularity_covector_carrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    regularity.fieldCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularRieszScale period
        hPeriod configuration data analysis chartData regularity state := by
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  have hDen : 1 + ‖remainder‖ ^ 2 ≠ 0 := by positivity
  change regularity.fieldCovector state (total - scale • remainder) = scale
  rw [map_sub, map_smul, smul_eq_mul]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_pairing]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_pairing]
  rw [real_inner_self_eq_norm_sq]
  dsimp only [scale]
  field_simp [hDen]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLFieldHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      (LLFieldGraphData period hPeriod configuration data analysis chartData
        state).baseCovector
          (LLFieldInclusion period hPeriod configuration data analysis
            chartData test) + regularity.fieldCovector state test := by
  let base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total := base + remainder
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  let carrierValue := total - scale • remainder
  have hCarrierValue := llFieldRegularity_covector_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  change regularity.fieldCovector state carrierValue = scale at hCarrierValue
  change inner Real
      (WithLp.toLp 2
        (((carrierValue : LLFieldHilbert period hPeriod configuration data
            analysis chartData) :
          LLCommonAmbient period hPeriod configuration data analysis),
          regularity.fieldCovector state carrierValue))
      (WithLp.toLp 2
        (((test : LLFieldHilbert period hPeriod configuration data analysis
            chartData) :
          LLCommonAmbient period hPeriod configuration data analysis),
          regularity.fieldCovector state test)) = _
  rw [llFieldGraphAmbient_inner_apply]
  calc
    _ = inner Real carrierValue test +
        scale * regularity.fieldCovector state test := by
      exact congrArg (fun value : Real =>
        inner Real carrierValue test +
          value * regularity.fieldCovector state test) hCarrierValue
    _ = _ := by
      have hSub : inner Real (total - scale • remainder) test =
          inner Real total test - inner Real (scale • remainder) test :=
        @inner_sub_left Real
          (LLFieldHilbert period hPeriod configuration data analysis chartData)
          inferInstance
          (llFieldFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llFieldFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          total (scale • remainder) test
      have hSmul : inner Real (scale • remainder) test =
          scale * inner Real remainder test :=
        @real_inner_smul_left
          (LLFieldHilbert period hPeriod configuration data analysis chartData)
          (llFieldFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llFieldFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          remainder test scale
      have hTotal : inner Real total test =
          inner Real base test + inner Real remainder test := by
        dsimp only [total]
        exact @inner_add_left Real
          (LLFieldHilbert period hPeriod configuration data analysis chartData)
          inferInstance
          (llFieldFixedSeminormedAddCommGroup period hPeriod configuration
            data analysis chartData)
          (llFieldFixedInnerProductSpace period hPeriod configuration data
            analysis chartData)
          base remainder test
      have hCarrierInner : inner Real carrierValue test =
          (inner Real base test + inner Real remainder test) -
            scale * inner Real remainder test := by
        dsimp only [carrierValue]
        calc
          _ = inner Real total test - inner Real (scale • remainder) test := hSub
          _ = inner Real total test - scale * inner Real remainder test :=
            congrArg (fun value : Real => inner Real total test - value) hSmul
          _ = (inner Real base test + inner Real remainder test) -
              scale * inner Real remainder test :=
            congrArg (fun value : Real =>
              value - scale * inner Real remainder test) hTotal
      have hBase : inner Real base test =
          (LLFieldGraphData period hPeriod configuration data analysis chartData
            state).baseCovector
            (LLFieldInclusion period hPeriod configuration data analysis
              chartData test) := by
        dsimp only [base]
        exact
          globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative_pairing
            period hPeriod configuration data analysis chartData state test
      have hRemainder : inner Real remainder test =
          regularity.fieldCovector state test := by
        dsimp only [remainder]
        exact
          globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_pairing
            period hPeriod configuration data analysis chartData regularity state
              test
      have hPairSum := congrArg₂ (fun first second : Real => first + second)
        hBase hRemainder
      have hScaled := congrArg (fun value : Real => scale * value) hRemainder
      have hDifference := congrArg₂ (fun first second : Real => first - second)
        hPairSum hScaled
      calc
        _ = ((inner Real base test + inner Real remainder test) -
              scale * inner Real remainder test) +
            scale * regularity.fieldCovector state test :=
          congrArg (fun value : Real =>
            value + scale * regularity.fieldCovector state test) hCarrierInner
        _ = (((LLFieldGraphData period hPeriod configuration data analysis
                chartData state).baseCovector
                (LLFieldInclusion period hPeriod configuration data analysis
                  chartData test) + regularity.fieldCovector state test) -
              scale * regularity.fieldCovector state test) +
            scale * regularity.fieldCovector state test :=
          congrArg (fun value : Real =>
            value + scale * regularity.fieldCovector state test) hDifference
        _ = _ := by ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact llFieldRegularity_covector_carrierValue period hPeriod
      configuration data analysis chartData regularity state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  letI : InnerProductSpace Real
      (LLFieldGraphHilbert period hPeriod configuration data analysis chartData
        state) :=
    llFieldGraphHilbertInnerProductSpace period hPeriod configuration data analysis
      chartData state
  letI : CompleteSpace
      (LLFieldGraphHilbert period hPeriod configuration data analysis chartData
        state) :=
    llFieldGraphHilbertCompleteSpace period hPeriod configuration data analysis
      chartData state
  refine @DenseRange.eq_of_inner_left
    (LLFieldGraphHilbert period hPeriod configuration data analysis chartData
      state)
    (LLFieldHilbert period hPeriod configuration data analysis chartData)
    Real inferInstance inferInstance
    (llFieldGraphHilbertInnerProductSpace period hPeriod configuration data
      analysis chartData state)
    _ _ _
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding_denseRange
      period hPeriod configuration data analysis chartData regularity state) ?_
  intro test
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      stateDependentAugmentedGraphCovector
        (LLFieldGraphData period hPeriod configuration data analysis chartData
          state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) := by
        exact stateDependentAugmentedGraphRieszResidual_pairing _ _
    _ = (LLFieldGraphData period hPeriod configuration data analysis chartData
          state).baseCovector
            (LLFieldInclusion period hPeriod configuration data analysis
              chartData test) + regularity.fieldCovector state test := by
        rfl
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
          test).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-- Gate 312: all three authentic LL graph residuals equal their explicit
fixed-carrier rank-one formulas. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_regular_graph_riesz_formula_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state =
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state =
          globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszCandidate
            period hPeriod configuration data analysis chartData regularity state ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state =
          globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszCandidate
            period hPeriod configuration data analysis chartData regularity state :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual_eq_regularFormula
      period hPeriod configuration data analysis chartData regularity state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual_eq_regularFormula
      period hPeriod configuration data analysis chartData regularity state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual_eq_regularFormula
      period hPeriod configuration data analysis chartData regularity state⟩

end RegularFormula
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRegularGraphRieszFormula4D
end JanusFormal
