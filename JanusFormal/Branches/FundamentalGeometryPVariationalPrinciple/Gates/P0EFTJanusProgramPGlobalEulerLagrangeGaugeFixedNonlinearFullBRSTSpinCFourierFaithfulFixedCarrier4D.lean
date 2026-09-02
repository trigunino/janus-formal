import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixAndPhysicalGhostPotentialData4D

/-!
# Fixed Hilbert carrier for the Fourier-faithful SpinC coordinate

The smooth SpinC tests have a state-independent closed carrier inside the
Fourier-faithful ambient Hilbert space. They embed into it densely and
injectively.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCarrier4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev SpinCTest :=
  Sector → D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- State-independent Fourier-faithful ambient space for the SpinC tests. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient :=
  WithLp 2
    (ProgramPPrimitiveSpinCMatterHilbert ×
      ProgramPPrimitiveSpinCMatterHilbert)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section SpinCCarrier

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

/-- Fixed faithful Fourier coordinate of a smooth SpinC test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap :
    SpinCTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap period
    hPeriod configuration data analysis chartData

/-- Closed state-independent carrier of the faithful SpinC coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedClosure :
    Submodule Real
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap
      period hPeriod configuration data analysis chartData)).topologicalClosure

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedClosure
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert
        period hPeriod configuration data analysis chartData) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap
        period hPeriod configuration data analysis chartData))

/-- Dense inclusion of smooth SpinC tests into the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding :
    SpinCTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert
        period hPeriod configuration data analysis chartData where
  toFun test :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap
        period hPeriod configuration data analysis chartData test,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap
          period hPeriod configuration data analysis chartData)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap
            period hPeriod configuration data analysis chartData) test)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar test := Subtype.ext (map_smul _ scalar test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseMap
      period hPeriod configuration data analysis chartData
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) =
        (LinearMap.range coordinate : Set
          GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test,
          ⟨test, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
        period hPeriod configuration data analysis chartData))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap_injective
      period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

/-- Gate 292: smooth SpinC tests have a fixed complete closed carrier with a
dense injective embedding. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_fourier_faithful_fixed_carrier_gate :
    DenseRange
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
          period hPeriod configuration data analysis chartData) ∧
      Function.Injective
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
          period hPeriod configuration data analysis chartData) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding_injective
      period hPeriod configuration data analysis chartData⟩

end SpinCCarrier
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCarrier4D
end JanusFormal
