import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingFourRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D

/-!
# Fixed paired-L² carrier for the full-BRST normal coordinate

Pure normal tests have a state-independent closed carrier in their faithful
two-sheet `L²` coordinate. They embed into it densely and injectively.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCarrier4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

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

local instance : IsFiniteMeasure
    (intrinsicCanonicalThroatVolumeMeasure
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- State-independent faithful paired-`L²` ambient space for normal tests. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPairedNormalL2 period hPeriod

/-- Fixed faithful paired-`L²` coordinate of a pure normal test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient
        period hPeriod :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap period
    hPeriod

/-- Closed state-independent carrier of the paired normal `L²` coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedClosure :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient
        period hPeriod) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap
      period hPeriod)).topologicalClosure

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedClosure period
    hPeriod

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert
        period hPeriod) := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient
        period hPeriod) := inferInstance
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap
        period hPeriod))

/-- Canonical continuous inclusion of the fixed normal carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedInclusionCLM :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert period
        hPeriod →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient
        period hPeriod :=
  Submodule.subtypeL
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedClosure period
      hPeriod)

/-- Dense inclusion of pure normal tests into the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert
        period hPeriod where
  toFun test :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap
        period hPeriod test,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap
          period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap
            period hPeriod) test)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar test := Subtype.ext (map_smul _ scalar test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
        period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedBaseMap period
      hPeriod
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
            period hPeriod) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient
            period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
            period hPeriod test,
          ⟨test, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient
        period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
        period hPeriod))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
        period hPeriod) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap_injective
      period hPeriod
  exact congrArg Subtype.val hEqual

/-- Gate 304: pure normal tests have a fixed complete closed paired-`L²`
carrier with a dense injective embedding. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_normal_paired_l2_fixed_carrier_gate :
    DenseRange
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
          period hPeriod) ∧
      Function.Injective
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
          period hPeriod) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_denseRange
      period hPeriod,
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_injective
      period hPeriod⟩

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCarrier4D
end JanusFormal
