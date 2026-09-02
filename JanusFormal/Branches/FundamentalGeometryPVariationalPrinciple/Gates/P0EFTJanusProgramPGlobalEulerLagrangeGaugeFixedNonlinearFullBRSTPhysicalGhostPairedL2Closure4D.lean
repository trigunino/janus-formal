import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D

/-!
# Fixed closed L² carrier for the physical full-BRST ghost

The faithful paired finite-frame coordinate has a state-independent closed
Hilbert carrier.  Original ghost tests embed densely and injectively into it.
This is the fixed domain on which a future continuous Euler covector family
must be constructed; no smooth extension is assumed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2Faithfulness4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GhostMeasure :=
  intrinsicCanonicalThroatVolumeMeasure period hPeriod

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

/-- State-independent ambient paired `L²` coordinate for physical ghosts. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D :=
  WithLp 2
    (PhysicalGhostFiniteFrameL2 period hPeriod ×
      PhysicalGhostFiniteFrameL2 period hPeriod)

private abbrev GhostTest :=
  GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod

/-- Closed range of the faithful paired physical-ghost `L²` coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
        period hPeriod) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
      period hPeriod)).topologicalClosure

/-- Hilbert carrier obtained from the closed paired `L²` range. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
    period hPeriod

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2CompleteSpace4D :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D
        period hPeriod) := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
        period hPeriod) := inferInstance
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
        period hPeriod))

/-- Canonical inclusion of algebraic physical-ghost tests into the fixed closed
paired `L²` carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding :
    GhostTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D
        period hPeriod where
  toFun ghost :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
        period hPeriod ghost,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
          period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
            period hPeriod) ghost)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar ghost := Subtype.ext (map_smul _ scalar ghost)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
        period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
      period hPeriod
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
            period hPeriod) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
            period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨ghost, rfl⟩, rfl⟩
      exact ⟨ghost, rfl⟩
    · rintro ⟨ghost, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
            period hPeriod ghost,
          ⟨ghost, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
        period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
        period hPeriod))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
        period hPeriod) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap_injective
      period hPeriod
  exact congrArg Subtype.val hEqual

/-- Gate 280: the faithful physical-ghost coordinate has a fixed complete
closed carrier with a dense injective test embedding. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_paired_l2_closure_gate :
    DenseRange
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
          period hPeriod) ∧
      Function.Injective
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
          period hPeriod) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding_denseRange
      period hPeriod,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding_injective
      period hPeriod⟩

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
end JanusFormal
