import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D

/-!
# Fixed-carrier formula for the normal graph residual

The smooth Robin and cross-block covectors determine the authentic normal
graph residual by an explicit two-covector Gram formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszFormula4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev NormalTest :=
  GlobalMinimalPhysicalNormalTest period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalThroatVolumeMeasure
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

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

private abbrev NormalAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient period
    hPeriod

private abbrev NormalHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert period
    hPeriod

private abbrev NormalRobinBase :=
  WithLp 2 (NormalAmbient period hPeriod × Real)

private abbrev NormalGraphAmbient :=
  WithLp 2 (NormalRobinBase period hPeriod × Real)

private abbrev NormalInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedInclusionCLM
    period hPeriod

private abbrev GraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
    period hPeriod configuration data analysis chartData state

private abbrev GraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphHilbert
    period hPeriod configuration data analysis chartData state

local instance normalHilbertCompleteSpace :
    CompleteSpace (NormalHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCompleteSpace
    period hPeriod

local instance graphHilbertCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (GraphHilbert period hPeriod configuration data analysis chartData state) :=
  stateDependentAugmentedGraphCompleteSpace
    (GraphData period hPeriod configuration data analysis chartData state)

/-- The fixed graph of the inclusion and Robin covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalHilbert period hPeriod →L[Real] NormalRobinBase period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (NormalAmbient period hPeriod) Real).symm.toContinuousLinearMap.comp
      ((NormalInclusion period hPeriod).prod
        (regularity.robinCovector state))

/-- The fixed graph of the inclusion, Robin covector and cross covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalHilbert period hPeriod →L[Real] NormalGraphAmbient period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (NormalRobinBase period hPeriod) Real).symm.toContinuousLinearMap.comp
      ((globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinGraph
          period hPeriod configuration data analysis chartData regularity state
        ).prod (regularity.crossCovector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : NormalTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
          period hPeriod test) =
      stateDependentAugmentedGraphLinearMap
        (GraphData period hPeriod configuration data analysis chartData state)
        test := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · exact regularity.robinRepresents state test
  · exact regularity.crossRepresents state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : NormalHilbert period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph
        period hPeriod configuration data analysis chartData regularity state value ∈
      stateDependentAugmentedGraphSubmodule
        (GraphData period hPeriod configuration data analysis chartData state) := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph
      period hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
      period hPeriod
  let raw := stateDependentAugmentedGraphLinearMap
    (GraphData period hPeriod configuration data analysis chartData state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_denseRange
      period hPeriod
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (NormalGraphAmbient period hPeriod))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨test, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw test

/-- Lift of the fixed graph into the authentic completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalHilbert period hPeriod →L[Real]
      GraphHilbert period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph
      period hPeriod configuration data analysis chartData regularity state
    ).codRestrict
      (stateDependentAugmentedGraphSubmodule
        (GraphData period hPeriod configuration data analysis chartData state))
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph_mem
        period hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : NormalTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
          period hPeriod test) =
      stateDependentAugmentedGraphEmbedding
        (GraphData period hPeriod configuration data analysis chartData state)
        test := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (GraphData period hPeriod configuration data analysis chartData state)).mono
  rintro result ⟨test, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
        period hPeriod test,
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state test⟩

private abbrev RobinRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
    period hPeriod configuration data analysis chartData regularity state

private abbrev CrossRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
    period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  (1 + ‖robin‖ ^ 2) * (1 + ‖cross‖ ^ 2) -
    inner Real robin cross ^ 2

private theorem normalRegularGramDeterminant_pos
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    0 < globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
      period hPeriod configuration data analysis chartData regularity state := by
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  have hCS : inner Real robin cross ^ 2 ≤ ‖robin‖ ^ 2 * ‖cross‖ ^ 2 := by
    simpa only [pow_two, real_inner_self_eq_norm_sq] using
      (real_inner_mul_inner_self_le robin cross)
  have hBase : 0 < 1 + ‖robin‖ ^ 2 + ‖cross‖ ^ 2 := by positivity
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
  dsimp only
  calc
    (1 + ‖robin‖ ^ 2) * (1 + ‖cross‖ ^ 2) -
          inner Real robin cross ^ 2 =
        (1 + ‖robin‖ ^ 2 + ‖cross‖ ^ 2) +
          (‖robin‖ ^ 2 * ‖cross‖ ^ 2 - inner Real robin cross ^ 2) := by ring
    _ > 0 := add_pos_of_pos_of_nonneg hBase (sub_nonneg.mpr hCS)

private theorem normalRegularGramDeterminant_ne_zero
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
      period hPeriod configuration data analysis chartData regularity state ≠ 0 :=
  ne_of_gt (normalRegularGramDeterminant_pos period hPeriod configuration data
    analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let total := robin + cross
  (inner Real robin total * (1 + ‖cross‖ ^ 2) -
      inner Real robin cross * inner Real cross total) /
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCrossScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let total := robin + cross
  ((1 + ‖robin‖ ^ 2) * inner Real cross total -
      inner Real robin cross * inner Real robin total) /
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCarrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalHilbert period hPeriod :=
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let robinScale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinScale
      period hPeriod configuration data analysis chartData regularity state
  let crossScale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCrossScale
      period hPeriod configuration data analysis chartData regularity state
  robin + cross - robinScale • robin - crossScale • cross

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GraphHilbert period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalGraphAmbient period hPeriod :=
  WithLp.toLp 2
    (WithLp.toLp 2
      (((globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state :
            NormalHilbert period hPeriod) : NormalAmbient period hPeriod),
        globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinScale
          period hPeriod configuration data analysis chartData regularity state),
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCrossScale
        period hPeriod configuration data analysis chartData regularity state)

private theorem normalRegular_covectors_carrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    regularity.robinCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinScale
        period hPeriod configuration data analysis chartData regularity state ∧
    regularity.crossCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCrossScale
        period hPeriod configuration data analysis chartData regularity state := by
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let total := robin + cross
  let determinant :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGramDeterminant
      period hPeriod configuration data analysis chartData regularity state
  let robinScale :=
    (inner Real robin total * (1 + ‖cross‖ ^ 2) -
      inner Real robin cross * inner Real cross total) / determinant
  let crossScale :=
    ((1 + ‖robin‖ ^ 2) * inner Real cross total -
      inner Real robin cross * inner Real robin total) / determinant
  have hDet : determinant ≠ 0 :=
    normalRegularGramDeterminant_ne_zero period hPeriod configuration data
      analysis chartData regularity state
  have hDetEq : determinant =
      (1 + ‖robin‖ ^ 2) * (1 + ‖cross‖ ^ 2) -
        inner Real robin cross ^ 2 := by
    rfl
  have hRobin (value : NormalHilbert period hPeriod) :
      regularity.robinCovector state value = inner Real robin value := by
    simpa only [robin, RobinRepresentative] using
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative_pairing
        period hPeriod configuration data analysis chartData regularity state value).symm
  have hCross (value : NormalHilbert period hPeriod) :
      regularity.crossCovector state value = inner Real cross value := by
    simpa only [cross, CrossRepresentative] using
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative_pairing
        period hPeriod configuration data analysis chartData regularity state value).symm
  constructor
  · change regularity.robinCovector state
      (total - robinScale • robin - crossScale • cross) = robinScale
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hRobin, hRobin, hRobin]
    rw [real_inner_self_eq_norm_sq]
    dsimp only [robinScale, crossScale]
    field_simp [hDet]
    rw [hDetEq]
    ring
  · change regularity.crossCovector state
      (total - robinScale • robin - crossScale • cross) = crossScale
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hCross, hCross, hCross]
    rw [← real_inner_comm cross robin, real_inner_self_eq_norm_sq]
    dsimp only [robinScale, crossScale]
    field_simp [hDet]
    rw [hDetEq]
    ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : NormalHilbert period hPeriod) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      regularity.robinCovector state test +
        regularity.crossCovector state test := by
  let robin := RobinRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let cross := CrossRepresentative period hPeriod configuration data analysis
    chartData regularity state
  let robinScale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularRobinScale
      period hPeriod configuration data analysis chartData regularity state
  let crossScale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularCrossScale
      period hPeriod configuration data analysis chartData regularity state
  let carrierValue := robin + cross - robinScale • robin - crossScale • cross
  have hValues := normalRegular_covectors_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  change regularity.robinCovector state carrierValue = robinScale ∧
    regularity.crossCovector state carrierValue = crossScale at hValues
  change inner Real
      (WithLp.toLp 2
        (WithLp.toLp 2
          (((carrierValue : NormalHilbert period hPeriod) :
            NormalAmbient period hPeriod),
            regularity.robinCovector state carrierValue),
          regularity.crossCovector state carrierValue))
      (WithLp.toLp 2
        (WithLp.toLp 2
          (((test : NormalHilbert period hPeriod) : NormalAmbient period hPeriod),
            regularity.robinCovector state test),
          regularity.crossCovector state test)) = _
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [Real.inner_apply]
  rw [hValues.1, hValues.2]
  change inner Real carrierValue test +
      robinScale * regularity.robinCovector state test +
      crossScale * regularity.crossCovector state test =
    regularity.robinCovector state test + regularity.crossCovector state test
  have hRobinSmul : inner Real (robinScale • robin) test =
      robinScale * inner Real robin test := by
    exact @real_inner_smul_left (NormalHilbert period hPeriod)
      inferInstance inferInstance robin test robinScale
  have hCrossSmul : inner Real (crossScale • cross) test =
      crossScale * inner Real cross test := by
    exact @real_inner_smul_left (NormalHilbert period hPeriod)
      inferInstance inferInstance cross test crossScale
  dsimp only [carrierValue]
  rw [inner_sub_left, inner_sub_left, inner_add_left]
  rw [hRobinSmul, hCrossSmul]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative_pairing]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative_pairing]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  have hValues := normalRegular_covectors_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · exact hValues.1
  · exact hValues.2

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  apply
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding_denseRange
      period hPeriod configuration data analysis chartData regularity state
      ).eq_of_inner_left Real
  intro test
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      stateDependentAugmentedGraphCovector
        (GraphData period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) := by
        exact stateDependentAugmentedGraphRieszResidual_pairing _ _
    _ = regularity.robinCovector state test +
          regularity.crossCovector state test := by
        rfl
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
          test).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual_eq_regularFormula]
  exact globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate_val
    period hPeriod configuration data analysis chartData regularity state

/-- Gate 306: the authentic normal graph residual equals its explicit fixed
two-covector Gram formula. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_normal_regular_graph_riesz_formula_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual_eq_regularFormula
    period hPeriod configuration data analysis chartData regularity state

end RegularFormula
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszFormula4D
end JanusFormal
