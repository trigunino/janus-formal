import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTResolvedNonminimalEulerSystem4D

/-!
# Graph-Riesz residual of the coupled Abelian potential equation

The Maxwell, physical cross-block and BRST terms are retained in one exact
covector.  Its value is added as a scalar graph coordinate, so the resulting
closed Hilbert graph has an exact separating Riesz residual.  No local PDE or
fixed-state-independent graph norm is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D

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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
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
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldPotentialGraphRieszResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpacePotentialGraphRieszResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldPotentialGraphRieszResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpacePotentialGraphRieszResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpacePotentialGraphRieszResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section PotentialGraphRieszResidual

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
    configuration data analysis chartData

private abbrev PairedPotential :=
  Sector → SmoothAbelianGaugePotential period hPeriod

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev AbelianGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10001) abelianGraphNormedAddCommGroupPotentialResidual :
    NormedAddCommGroup (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) abelianGraphNormedSpacePotentialResidual :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) abelianGraphAddCommGroupPotentialResidual :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedAddCommGroupPotentialResidual period hPeriod
    configuration data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) abelianGraphTopologicalSpacePotentialResidual :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedAddCommGroupPotentialResidual period hPeriod
    configuration data).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) abelianGraphModulePotentialResidual :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedSpacePotentialResidual period hPeriod configuration data).toModule

local instance abelianGraphCompleteSpacePotentialResidual :
    CompleteSpace (AbelianGraph period hPeriod configuration data) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev PotentialGraphAmbient :=
  WithLp 2 (AbelianGraph period hPeriod configuration data × Real)

/-- Smooth potential tests with their full coupled Euler value as graph
coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedPotential period hPeriod →ₗ[Real]
      PotentialGraphAmbient period hPeriod configuration data where
  toFun potential := WithLp.toLp 2
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
          period hPeriod potential),
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
        hPeriod configuration data analysis chartData state potential)
  map_add' first second := by
    apply WithLp.ofLp_injective
    simp
  map_smul' scalar potential := by
    apply WithLp.ofLp_injective
    simp

/-- Closed Hilbert graph generated by smooth coupled-potential tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphSubmodule
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Submodule Real (PotentialGraphAmbient period hPeriod configuration data) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
      hPeriod configuration data analysis chartData state)).topologicalClosure

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphSubmodule period
    hPeriod configuration data analysis chartData state

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphCompleteSpace
    (state : FullChart period hPeriod configuration data analysis chartData) :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state) := by
  letI : CompleteSpace
      (PotentialGraphAmbient period hPeriod configuration data) := inferInstance
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
        hPeriod configuration data analysis chartData state))

/-- Dense inclusion of smooth potential tests into their completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedPotential period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state where
  toFun potential :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
        hPeriod configuration data analysis chartData state potential,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
          hPeriod configuration data analysis chartData state)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
            hPeriod configuration data analysis chartData state) potential)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar potential := Subtype.ext (map_smul _ scalar potential)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_denseRange
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
        hPeriod configuration data analysis chartData state) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let graph :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
      hPeriod configuration data analysis chartData state
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding
            period hPeriod configuration data analysis chartData state) =
        (LinearMap.range graph :
          Set (PotentialGraphAmbient period hPeriod configuration data)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨potential, rfl⟩, rfl⟩
      exact ⟨potential, rfl⟩
    · rintro ⟨potential, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding
            period hPeriod configuration data analysis chartData state potential,
          ⟨potential, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (PotentialGraphAmbient period hPeriod configuration data)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
        hPeriod configuration data analysis chartData state))
  rw [hRange]

/-- Continuous scalar Euler coordinate on the completed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state →L[Real] Real :=
  (WithLp.sndL 2 Real
      (AbelianGraph period hPeriod configuration data) Real).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphSubmodule period
      hPeriod configuration data analysis chartData state).subtypeL

/-- Exact Riesz representative of the full coupled potential covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphCompleteSpace period
      hPeriod configuration data analysis chartData state
  exact
    (InnerProductSpace.toDual Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state)).symm
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphCovector period
        hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert
      period hPeriod configuration data analysis chartData state) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphCovector period
        hPeriod configuration data analysis chartData state test := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
        hPeriod configuration data analysis chartData state) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphCompleteSpace period
      hPeriod configuration data analysis chartData state
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
  exact InnerProductSpace.toDual_symm_apply

def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (residual : GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert
      period hPeriod configuration data analysis chartData state)
    (test : PairedPotential period hPeriod) : Real :=
  inner Real residual
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
      hPeriod configuration data analysis chartData state test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_apply_eq_graphResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PairedPotential period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
        hPeriod configuration data analysis chartData state test =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_pairing]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing_separates
    (state : FullChart period hPeriod configuration data analysis chartData)
    (residual : GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert
      period hPeriod configuration data analysis chartData state) :
    (∀ test : PairedPotential period hPeriod,
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing
          period hPeriod configuration data analysis chartData state residual
          test = 0) ↔ residual = 0 := by
  constructor
  · intro hPairing
    apply
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_denseRange
        period hPeriod configuration data analysis chartData state
        ).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    exact hPairing test
  · rintro rfl test
    simp [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing]

def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualRepresentation
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
        hPeriod configuration data analysis chartData state) where
  Residual :=
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphHilbert period
      hPeriod configuration data analysis chartData state
  zeroResidual := 0
  residual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual period
      hPeriod configuration data analysis chartData state
  pairing :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing
      period hPeriod configuration data analysis chartData state
  represents := fun test =>
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_apply_eq_graphResidualPairing
      period hPeriod configuration data analysis chartData state test
  separates :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualPairing_separates
      period hPeriod configuration data analysis chartData state
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq_zero_iff_graphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphResidualRepresentation
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_potentialGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq_zero_iff_graphResidual
    period hPeriod configuration data analysis chartData state).mp
      (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_potentialEuler_eq_zero
        period hPeriod configuration data analysis chartData state hCritical)

/-- Gate 251: the full coupled Abelian potential equation has an exact
state-dependent separating residual on its closed Hilbert graph. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_potential_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq_zero_iff_graphResidual
    period hPeriod configuration data analysis chartData state

end PotentialGraphRieszResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
end JanusFormal
