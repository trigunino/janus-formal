import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D

/-!
# Explicit regular graph formula for the coupled potential residual

Conditional on the fixed-carrier Euler datum, the authentic moving graph is
realized densely by a continuous fixed-carrier graph and its Riesz residual has
an explicit ambient formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszFormula4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

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

section RieszFormula

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

private abbrev PairedPotential :=
  Sector → SmoothAbelianGaugePotential period hPeriod

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev AbelianGraph :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient period
    hPeriod configuration data

private abbrev PotentialClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedClosure period
    hPeriod configuration data

private abbrev PotentialHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedHilbert period
    hPeriod configuration data

private abbrev PotentialGraphAmbient :=
  WithLp 2 (AbelianGraph period hPeriod configuration data × Real)

@[implicit_reducible]
local instance (priority := 10001) abelianGraphNormedAddCommGroup :
    NormedAddCommGroup (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) abelianGraphNormedSpace :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) abelianGraphAddCommGroup :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedAddCommGroup period hPeriod configuration data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) abelianGraphTopologicalSpace :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedAddCommGroup period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) abelianGraphModule :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedSpace period hPeriod configuration data).toModule

local instance abelianGraphCompleteSpace :
    CompleteSpace (AbelianGraph period hPeriod configuration data) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance potentialHilbertCompleteSpace :
    CompleteSpace (PotentialHilbert period hPeriod configuration data) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCompleteSpace period
    hPeriod configuration data

/-- Continuous fixed-carrier graph of the regular potential Euler covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PotentialHilbert period hPeriod configuration data →L[Real]
      PotentialGraphAmbient period hPeriod configuration data :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (AbelianGraph period hPeriod configuration data) Real).symm.toContinuousLinearMap.comp
    ((PotentialClosure period hPeriod configuration data).subtypeL.prod
      (regularity.covector state))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (potential : PairedPotential period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph period
        hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data potential) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
        hPeriod configuration data analysis chartData state potential := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simpa [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph,
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding,
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap,
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap]
      using regularity.represents state potential

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph_mem
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (value : PotentialHilbert period hPeriod configuration data) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph period
        hPeriod configuration data analysis chartData regularity state value ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphSubmodule period
        hPeriod configuration data analysis chartData state := by
  let graph := globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph
    period hPeriod configuration data analysis chartData regularity state
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
      period hPeriod configuration data
  let raw := globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap
    period hPeriod configuration data analysis chartData state
  have hDense : Dense (Set.range embedding) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding_denseRange
      period hPeriod configuration data
  have hNear : Set.range graph ⊆ closure (graph '' Set.range embedding) :=
    graph.continuous.range_subset_closure_image_dense hDense
  change graph value ∈ closure (LinearMap.range raw : Set
    (PotentialGraphAmbient period hPeriod configuration data))
  apply (closure_mono ?_) (hNear ⟨value, rfl⟩)
  rintro result ⟨lifted, ⟨potential, rfl⟩, rfl⟩
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph_denseEmbedding]
  exact LinearMap.mem_range_self raw potential

/-- Lift of the regular graph into the authentic completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PotentialHilbert period hPeriod configuration data →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph period
      hPeriod configuration data analysis chartData regularity state).codRestrict
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphSubmodule period
      hPeriod configuration data analysis chartData state)
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph_mem period
      hPeriod configuration data analysis chartData regularity state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding_denseEmbedding
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (potential : PairedPotential period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data potential) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
        hPeriod configuration data analysis chartData state potential := by
  apply Subtype.ext
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraph_denseEmbedding
      period hPeriod configuration data analysis chartData regularity state
        potential

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding_denseRange
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding
        period hPeriod configuration data analysis chartData regularity state) := by
  apply (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_denseRange
    period hPeriod configuration data analysis chartData state).mono
  rintro result ⟨potential, rfl⟩
  exact
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
        period hPeriod configuration data potential,
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding_denseEmbedding
        period hPeriod configuration data analysis chartData regularity state
          potential⟩

def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  (1 + ‖globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
    period hPeriod configuration data analysis chartData regularity state‖ ^ 2)⁻¹

def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
      hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state •
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
        period hPeriod configuration data analysis chartData regularity state)

def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PotentialGraphAmbient period hPeriod configuration data :=
  let representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  WithLp.toLp 2
    (((scale • representative : PotentialHilbert period hPeriod configuration
        data) : AbelianGraph period hPeriod configuration data),
      scale * ‖representative‖ ^ 2)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PotentialHilbert period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
            test) = regularity.covector state test := by
  let representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := (1 + ‖representative‖ ^ 2)⁻¹
  change inner Real
      (WithLp.toLp 2
        (((scale • representative : PotentialHilbert period hPeriod
            configuration data) : AbelianGraph period hPeriod configuration
              data), regularity.covector state (scale • representative)))
      (WithLp.toLp 2
        ((test : AbelianGraph period hPeriod configuration data),
          regularity.covector state test)) = regularity.covector state test
  rw [WithLp.prod_inner_apply]
  simp only [map_smul, smul_eq_mul, Real.inner_apply]
  rw [← (PotentialClosure period hPeriod configuration data).coe_inner]
  have hScaledInner : inner Real (scale • representative) test =
      scale * regularity.covector state test := by
    calc
      _ = scale * inner Real representative test :=
        real_inner_smul_left representative test scale
      _ = _ := congrArg (scale * ·)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative_pairing
          period hPeriod configuration data analysis chartData regularity state
            test)
  have hSelf : regularity.covector state representative =
      ‖representative‖ ^ 2 := by
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative_pairing]
    exact real_inner_self_eq_norm_sq representative
  rw [hScaledInner, hSelf]
  dsimp only [scale, representative]
  have hDen : 1 +
      ‖globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
        period hPeriod configuration data analysis chartData regularity state‖ ^
          2 ≠ 0 := by
    positivity
  field_simp [hDen]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  let representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · change regularity.covector state (scale • representative) =
        scale * ‖representative‖ ^ 2
    rw [map_smul, smul_eq_mul,
      ← globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative_pairing,
      real_inner_self_eq_norm_sq]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual period
        hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  apply (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_denseRange
    period hPeriod configuration data analysis chartData state).eq_of_inner_left
      Real
  intro potential
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding
          period hPeriod configuration data analysis chartData state potential) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
        hPeriod configuration data analysis chartData state potential := by
      simpa [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing]
        using
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_apply_eq_graphResidualPairing
            period hPeriod configuration data analysis chartData state
              potential).symm
    _ = regularity.covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data potential) :=
      (regularity.represents state potential).symm
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
            period hPeriod configuration data potential)) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data potential)).symm
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding
          period hPeriod configuration data analysis chartData state potential) := by
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphEmbedding_denseEmbedding]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual period
        hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-- Gate 289: the authentic potential graph residual equals its explicit
fixed-carrier regular formula. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_potential_regular_graph_riesz_formula_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual period
        hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_eq_regularFormula
    period hPeriod configuration data analysis chartData regularity state

end RieszFormula
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszFormula4D
end JanusFormal
