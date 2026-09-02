import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulSpectralBaseRegularity4D

/-!
# Fixed-carrier formula for the Fourier-faithful SpinC graph residual

The canonical spectral-base Riesz representative and a regular cross-block
remainder determine the authentic state-dependent graph residual by the exact
rank-one graph formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszFormula4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulSpectralBaseRegularity4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev SpinCTest :=
  Sector → D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

private abbrev SpinCBase :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient

private abbrev SpinCGraphAmbient :=
  WithLp 2 (SpinCBase × Real)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance matterHilbertRealInnerProductSpaceSpinCRegularFormula :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

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

private abbrev SpinCHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert
    period hPeriod configuration data analysis chartData

private abbrev SpinCClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedClosure
    period hPeriod configuration data analysis chartData

private abbrev GraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
    period hPeriod configuration data analysis chartData state

private abbrev GraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphHilbert
    period hPeriod configuration data analysis chartData state

local instance spinCHilbertCompleteSpace :
    CompleteSpace
      (SpinCHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCompleteSpace
    period hPeriod configuration data analysis chartData

local instance graphHilbertCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (GraphHilbert period hPeriod configuration data analysis chartData state) :=
  stateDependentAugmentedGraphCompleteSpace
    (GraphData period hPeriod configuration data analysis chartData state)

/-- Continuous graph of the regular cross-block remainder on the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
      SpinCGraphAmbient :=
  (WithLp.prodContinuousLinearEquiv 2 Real SpinCBase Real
    ).symm.toContinuousLinearMap.comp
      ((SpinCClosure period hPeriod configuration data analysis chartData
        ).subtypeL.prod (regularity.covector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : SpinCTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphLinearMap
        (GraphData period hPeriod configuration data analysis chartData state)
        test := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · change regularity.covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      (GraphData period hPeriod configuration data analysis chartData state
        ).remainder test
    exact regularity.represents state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : SpinCHilbert period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph
        period hPeriod configuration data analysis chartData regularity state value ∈
      stateDependentAugmentedGraphSubmodule
        (GraphData period hPeriod configuration data analysis chartData state) := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph
      period hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
      period hPeriod configuration data analysis chartData
  let raw := stateDependentAugmentedGraphLinearMap
    (GraphData period hPeriod configuration data analysis chartData state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set SpinCGraphAmbient)
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨test, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw test

/-- Lift of the fixed regular graph into the authentic completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
      GraphHilbert period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph
      period hPeriod configuration data analysis chartData regularity state
    ).codRestrict
      (stateDependentAugmentedGraphSubmodule
        (GraphData period hPeriod configuration data analysis chartData state))
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph_mem
        period hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : SpinCTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      stateDependentAugmentedGraphEmbedding
        (GraphData period hPeriod configuration data analysis chartData state)
        test := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (GraphData period hPeriod configuration data analysis chartData state)).mono
  rintro result ⟨test, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
        period hPeriod configuration data analysis chartData test,
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state test⟩

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularTotalRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state +
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  inner Real remainder total / (1 + ‖remainder‖ ^ 2)

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularCarrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCHilbert period hPeriod configuration data analysis chartData :=
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  total - scale • remainder

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GraphHilbert period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCGraphAmbient :=
  WithLp.toLp 2
    (((globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularCarrierValue
        period hPeriod configuration data analysis chartData regularity state :
          SpinCHilbert period hPeriod configuration data analysis chartData) :
        SpinCBase),
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state)

private theorem regularity_covector_carrierValue
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    regularity.covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularCarrierValue
          period hPeriod configuration data analysis chartData regularity state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularRieszScale
        period hPeriod configuration data analysis chartData regularity state := by
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularTotalRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  have hDen : 1 + ‖remainder‖ ^ 2 ≠ 0 := by positivity
  change regularity.covector state (total - scale • remainder) = scale
  rw [map_sub, map_smul, smul_eq_mul]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_pairing]
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_pairing]
  rw [real_inner_self_eq_norm_sq]
  dsimp only [scale]
  field_simp [hDen]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : SpinCHilbert period hPeriod configuration data analysis chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      (GraphData period hPeriod configuration data analysis chartData state
        ).baseCovector
          ((SpinCClosure period hPeriod configuration data analysis chartData
            ).subtypeL test) + regularity.covector state test := by
  let base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData state
  let remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let total := base + remainder
  let scale := inner Real remainder total / (1 + ‖remainder‖ ^ 2)
  let carrierValue := total - scale • remainder
  have hCarrierValue := regularity_covector_carrierValue period hPeriod
    configuration data analysis chartData regularity state
  change regularity.covector state carrierValue = scale at hCarrierValue
  change inner Real
      (WithLp.toLp 2
        (((carrierValue : SpinCHilbert period hPeriod configuration data analysis
            chartData) : SpinCBase), regularity.covector state carrierValue))
      (WithLp.toLp 2
        (((test : SpinCHilbert period hPeriod configuration data analysis
            chartData) : SpinCBase), regularity.covector state test)) = _
  rw [WithLp.prod_inner_apply]
  simp only [Real.inner_apply]
  rw [hCarrierValue]
  rw [← (SpinCClosure period hPeriod configuration data analysis chartData
    ).coe_inner]
  dsimp only [carrierValue, total]
  rw [inner_sub_left, real_inner_smul_left, inner_add_left]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative_pairing]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_pairing]
  ring

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact regularity_covector_carrierValue period hPeriod configuration data
      analysis chartData regularity state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  apply
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding_denseRange
      period hPeriod configuration data analysis chartData regularity state
      ).eq_of_inner_left Real
  intro test
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) =
      stateDependentAugmentedGraphCovector
        (GraphData period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) := by
        exact stateDependentAugmentedGraphRieszResidual_pairing _ _
    _ = (GraphData period hPeriod configuration data analysis chartData state
          ).baseCovector
            ((SpinCClosure period hPeriod configuration data analysis chartData
              ).subtypeL test) + regularity.covector state test := by
        rfl
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
          test).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-- Gate 295: the authentic Fourier-faithful SpinC graph residual equals its
explicit fixed-carrier rank-one formula. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_fourier_faithful_regular_graph_riesz_formula_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual_eq_regularFormula
    period hPeriod configuration data analysis chartData regularity state

end RegularFormula
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszFormula4D
end JanusFormal
