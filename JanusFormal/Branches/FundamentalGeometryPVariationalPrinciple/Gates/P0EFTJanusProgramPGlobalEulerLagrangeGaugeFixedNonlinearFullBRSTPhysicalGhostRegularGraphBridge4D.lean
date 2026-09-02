import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientExtension4D

/-!
# Regular physical-ghost graph bridge

Conditional on the physical-ghost Euler regularity datum, the algebraic
augmented graph factors through a continuous graph map on the fixed closed
paired `L²` carrier.  Its lift into the original completed graph has dense
range.  Existence of the regularity datum is not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GhostMeasure :=
  intrinsicCanonicalThroatVolumeMeasure period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure (GhostMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

section RegularGraph

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

private abbrev PhysicalGhostCarrier :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
    period hPeriod

private abbrev PhysicalGhostClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
    period hPeriod

private abbrev PhysicalGhostHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D
    period hPeriod

private abbrev PhysicalGhostEulerBase :=
  WithLp 2 (PhysicalGhostCarrier period hPeriod × Real)

private abbrev PhysicalGhostGraphAmbient :=
  WithLp 2 (PhysicalGhostEulerBase period hPeriod × Real)

local instance physicalGhostHilbertCompleteSpace :
    CompleteSpace (PhysicalGhostHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2CompleteSpace4D
    period hPeriod

/-- Continuous inner graph of the regular Euler covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularInnerGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PhysicalGhostHilbert period hPeriod →L[Real]
      PhysicalGhostEulerBase period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (PhysicalGhostCarrier period hPeriod) Real).symm.toContinuousLinearMap.comp
    ((PhysicalGhostClosure period hPeriod).subtypeL.prod
      (regularity.covector state))

/-- Continuous augmented graph, with the authentic BRST remainder equal to
zero. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PhysicalGhostHilbert period hPeriod →L[Real]
      PhysicalGhostGraphAmbient period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (PhysicalGhostEulerBase period hPeriod) Real).symm.toContinuousLinearMap.comp
    ((globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularInnerGraph
        period hPeriod configuration data analysis chartData regularity state).prod
      (0 : PhysicalGhostHilbert period hPeriod →L[Real] Real))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (ghost : GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
          period hPeriod ghost) =
      stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
          period hPeriod configuration data analysis chartData state) ghost := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · simpa [
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph,
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularInnerGraph,
        stateDependentAugmentedGraphLinearMap,
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData,
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap]
        using (regularity.represents state ghost).trans
          (congrArg (fun covector => covector ghost)
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector_eq
              period hPeriod configuration data analysis chartData state))
  · rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : PhysicalGhostHilbert period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph
        period hPeriod configuration data analysis chartData regularity state value ∈
      stateDependentAugmentedGraphSubmodule
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph
      period hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
      period hPeriod
  let raw :=
    stateDependentAugmentedGraphLinearMap
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
        period hPeriod configuration data analysis chartData state)
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding_denseRange
      period hPeriod
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (PhysicalGhostGraphAmbient period hPeriod))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨ghost, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw ghost

/-- Lift of the continuous regular graph into the original completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PhysicalGhostHilbert period hPeriod →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphHilbert
        period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph
      period hPeriod configuration data analysis chartData regularity state).codRestrict
    (stateDependentAugmentedGraphSubmodule
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
        period hPeriod configuration data analysis chartData state))
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph_mem
      period hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (ghost : GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
          period hPeriod ghost) =
      stateDependentAugmentedGraphEmbedding
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
          period hPeriod configuration data analysis chartData state) ghost := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularAugmentedGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state ghost

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (stateDependentAugmentedGraphEmbedding_denseRange
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
      period hPeriod configuration data analysis chartData state)).mono
  rintro result ⟨ghost, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
        period hPeriod ghost,
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state ghost⟩

/-- Gate 283: the regular fixed-carrier graph densely realizes the authentic
completed physical-ghost augmented graph. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_regular_graph_bridge_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding_denseRange
    period hPeriod configuration data analysis chartData regularity state

end RegularGraph
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphBridge4D
end JanusFormal
