import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenAndPhysicalGhostData4D

/-!
# Fixed Hilbert carrier for the coupled Abelian potential

The potential-only smooth directions have a state-independent closed carrier
inside the complete Abelian off-shell graph. They embed into it densely and
injectively.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialFixedCarrier4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D

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

section PotentialCarrier

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)

private abbrev PairedPotential :=
  Sector → SmoothAbelianGaugePotential period hPeriod

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev AbelianGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

/-- State-independent ambient Abelian graph containing potential-only tests. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient :=
  AbelianGraph period hPeriod configuration data

local instance abelianGraphCompleteSpacePotentialCarrier :
    CompleteSpace (AbelianGraph period hPeriod configuration data) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

/-- Fixed potential-only coordinate inside the complete Abelian graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap :
    PairedPotential period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient period
        hPeriod configuration data :=
  (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data)).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
      period hPeriod)

/-- Closed state-independent carrier of the potential-only coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedClosure :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient period
        hPeriod configuration data) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap period
      hPeriod configuration data)).topologicalClosure

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedClosure period
    hPeriod configuration data

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedHilbert period
        hPeriod configuration data) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap period
        hPeriod configuration data))

/-- Dense inclusion of smooth potential-only tests into the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding :
    PairedPotential period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedHilbert period
        hPeriod configuration data where
  toFun potential :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap period
        hPeriod configuration data potential,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap period
          hPeriod configuration data)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap
            period hPeriod configuration data) potential)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar potential := Subtype.ext (map_smul _ scalar potential)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
        period hPeriod configuration data) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedBaseMap period
      hPeriod configuration data
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
            period hPeriod configuration data) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient
            period hPeriod configuration data)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨potential, rfl⟩, rfl⟩
      exact ⟨potential, rfl⟩
    · rintro ⟨potential, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
            period hPeriod configuration data potential,
          ⟨potential, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient period
        hPeriod configuration data)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
        period hPeriod configuration data))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
        period hPeriod configuration data) := by
  intro first second hEqual
  have hBase := congrArg Subtype.val hEqual
  have hState :
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
          period hPeriod first =
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
          period hPeriod second := by
    apply globalPairedAbelianOffShellSmoothEmbedding_injective period hPeriod
      (BaseMetric period hPeriod configuration data)
    exact hBase
  exact congrArg GlobalPairedAbelianBRSTState.potential hState

/-- Gate 287: potential-only tests have a fixed complete closed carrier with a
dense injective embedding. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_potential_fixed_carrier_gate :
    DenseRange
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data) ∧
      Function.Injective
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding_denseRange
      period hPeriod configuration data,
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding_injective
      period hPeriod configuration data⟩

end PotentialCarrier
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialFixedCarrier4D
end JanusFormal
