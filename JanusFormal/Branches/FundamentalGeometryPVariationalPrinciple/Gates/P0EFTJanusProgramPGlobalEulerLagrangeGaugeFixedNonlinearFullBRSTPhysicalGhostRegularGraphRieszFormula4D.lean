import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphBridge4D

/-!
# Explicit physical-ghost regular-graph Riesz formula

Conditional on the regular Euler-covector datum, this file identifies the
authentic completed augmented-graph residual with its explicit fixed-carrier
Riesz formula.  Existence of the datum is not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszFormula4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphBridge4D

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

private abbrev PhysicalGhostHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D
    period hPeriod

private abbrev PhysicalGhostCarrier :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
    period hPeriod

local instance physicalGhostHilbertCompleteSpace :
    CompleteSpace (PhysicalGhostHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2CompleteSpace4D
    period hPeriod

def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularRieszScale
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) : Real :=
  (1 + ‖globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
    period hPeriod configuration data analysis chartData regularity state‖ ^ 2)⁻¹

/-- Explicit candidate in the authentic completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
    period hPeriod configuration data analysis chartData regularity state
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state •
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
        period hPeriod configuration data analysis chartData regularity state)

/-- State-dependent graph residual written entirely in the fixed ambient
carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    WithLp 2
      (WithLp 2 (PhysicalGhostCarrier period hPeriod × Real) × Real) :=
  let representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  WithLp.toLp 2
    (WithLp.toLp 2
      ((((scale • representative : PhysicalGhostHilbert period hPeriod) :
          PhysicalGhostCarrier period hPeriod),
        scale * ‖representative‖ ^ 2)),
      (0 : Real))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PhysicalGhostHilbert period hPeriod) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state test) =
      regularity.covector state test := by
  let representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale := (1 + ‖representative‖ ^ 2)⁻¹
  change inner Real
      (WithLp.toLp 2
        ((WithLp.toLp 2
          (((scale • representative : PhysicalGhostHilbert period hPeriod) :
              PhysicalGhostCarrier period hPeriod),
            regularity.covector state (scale • representative))),
          (0 : Real)))
      (WithLp.toLp 2
        ((WithLp.toLp 2
          ((test : PhysicalGhostCarrier period hPeriod),
            regularity.covector state test)),
          (0 : Real))) =
      regularity.covector state test
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [inner_zero_left, add_zero, map_smul, smul_eq_mul,
    Real.inner_apply]
  rw [← (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
      period hPeriod).coe_inner]
  have hScaledInner : inner Real (scale • representative) test =
      scale * regularity.covector state test := by
    calc
      _ = scale * inner Real representative test :=
        real_inner_smul_left representative test scale
      _ = _ := congrArg (scale * ·)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_pairing
          period hPeriod configuration data analysis chartData regularity state test)
  have hSelf : regularity.covector state representative = ‖representative‖ ^ 2 := by
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_pairing]
    exact real_inner_self_eq_norm_sq representative
  rw [hScaledInner, hSelf]
  dsimp only [scale, representative]
  have hDen : 1 +
      ‖globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
        period hPeriod configuration data analysis chartData regularity state‖ ^ 2 ≠ 0 := by
    positivity
  field_simp [hDen]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate_val
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  let representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
      period hPeriod configuration data analysis chartData regularity state
  let scale :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularRieszScale
      period hPeriod configuration data analysis chartData regularity state
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · change regularity.covector state (scale • representative) =
        scale * ‖representative‖ ^ 2
      rw [map_smul, smul_eq_mul,
        ← globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_pairing,
        real_inner_self_eq_norm_sq]
  · rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state := by
  let graphData :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
      period hPeriod configuration data analysis chartData state
  apply (stateDependentAugmentedGraphEmbedding_denseRange graphData).eq_of_inner_left Real
  intro ghost
  let embedding :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
      period hPeriod
  calc
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state)
        (stateDependentAugmentedGraphEmbedding graphData ghost) =
      stateDependentAugmentedTotalCovector graphData ghost := by
        simpa [graphData,
          globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual,
          stateDependentAugmentedGraphResidualPairing] using
          (stateDependentAugmentedTotalCovector_apply_eq_residualPairing
            graphData ghost).symm
    _ = globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
          period hPeriod configuration data analysis chartData state ghost := by
        exact congrArg (fun covector => covector ghost)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_l2AugmentedTotalCovector
            period hPeriod configuration data analysis chartData state).symm
    _ = regularity.covector state (embedding ghost) :=
      (regularity.represents state ghost).symm
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding
          period hPeriod configuration data analysis chartData regularity state
          (embedding ghost)) :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate_pairing
        period hPeriod configuration data analysis chartData regularity state
        (embedding ghost)).symm
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
          period hPeriod configuration data analysis chartData regularity state)
        (stateDependentAugmentedGraphEmbedding graphData ghost) := by
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphEmbedding_denseEmbedding]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual_val_eq_regularFormula
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual_eq_regularFormula]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate_val
      period hPeriod configuration data analysis chartData regularity state

/-- Gate 284: the authentic physical-ghost graph residual has the explicit
fixed-carrier Riesz formula. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_regular_graph_riesz_formula_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszCandidate
        period hPeriod configuration data analysis chartData regularity state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual_eq_regularFormula
    period hPeriod configuration data analysis chartData regularity state

end RieszFormula
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszFormula4D
end JanusFormal
