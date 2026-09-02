import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianResolvedTwoEquationStrongSystem4D

/-!
# Strong graph-Riesz residual of the paired Abelian ghost equation

The ghost tests generate a closed Hilbert subspace of the completed Abelian
off-shell graph. Restricting the genuine Hessian covector to this subspace and
applying Riesz gives an exact separating residual. No unsupported `L²`
Faddeev--Popov adjoint formula is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAbelianGhostGraphRieszResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceAbelianGhostGraphRieszResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAbelianGhostGraphRieszResidual :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAbelianGhostGraphRieszResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAbelianGhostGraphRieszResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev PairedGhost :=
  Sector → GlobalAbelianGhostField period hPeriod

/-- Pure paired ghost inclusion into the smooth Abelian BRST state. -/
def globalPairedAbelianPureGhostStateLinearMap :
    PairedGhost period hPeriod →ₗ[Real]
      GlobalPairedAbelianBRSTState period hPeriod where
  toFun ghost :=
    { potential := 0
      nonminimal := fun sector => ⟨ghost sector, ⟨0⟩, ⟨0⟩⟩ }
  map_add' first second := by
    apply GlobalPairedAbelianBRSTState.ext
    · funext sector
      simp
    · funext sector
      apply GlobalAbelianNonminimalFields.ext
      · apply GlobalAbelianGhostField.ext
        change
          (first sector + second sector).field =
            (first sector).field + (second sector).field
        rfl
      · apply GlobalAbelianAntighostField.ext
        change
          (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) = 0 + 0
        simp
      · apply GlobalAbelianNakanishiLautrupField.ext
        change
          (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) = 0 + 0
        simp
  map_smul' scalar ghost := by
    apply GlobalPairedAbelianBRSTState.ext
    · funext sector
      simp
    · funext sector
      apply GlobalAbelianNonminimalFields.ext
      · apply GlobalAbelianGhostField.ext
        change
          (scalar • ghost sector).field = scalar • (ghost sector).field
        rfl
      · apply GlobalAbelianAntighostField.ext
        change
          (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) =
            scalar • 0
        simp
      · apply GlobalAbelianNakanishiLautrupField.ext
        change
          (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) =
            scalar • 0
        simp

/-- Pure ghost tests mapped into the completed off-shell graph. -/
def globalPairedAbelianPureGhostGraphLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    PairedGhost period hPeriod →ₗ[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric).comp
    (globalPairedAbelianPureGhostStateLinearMap period hPeriod)

/-- Closed Hilbert subspace generated by pure smooth ghost tests. -/
def globalPairedAbelianPureGhostGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  (LinearMap.range
    (globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric)
    ).topologicalClosure

abbrev GlobalPairedAbelianPureGhostGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalPairedAbelianPureGhostGraphSubmodule period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) globalPairedAbelianOffShellGraphNormedAddCommGroupAbelianGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10001) globalPairedAbelianOffShellGraphNormedSpaceAbelianGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10002) globalPairedAbelianOffShellGraphAddCommGroupAbelianGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  (globalPairedAbelianOffShellGraphNormedAddCommGroupAbelianGhostResidual
    period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) globalPairedAbelianOffShellGraphTopologicalSpaceAbelianGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  (globalPairedAbelianOffShellGraphNormedAddCommGroupAbelianGhostResidual
    period hPeriod metric).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) globalPairedAbelianOffShellGraphModuleAbelianGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  (globalPairedAbelianOffShellGraphNormedSpaceAbelianGhostResidual
    period hPeriod metric).toModule

local instance globalPairedAbelianOffShellGraphCompleteSpaceAbelianGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

@[implicit_reducible]
def globalPairedAbelianPureGhostGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalPairedAbelianPureGhostGraphHilbert period hPeriod metric) := by
  unfold GlobalPairedAbelianPureGhostGraphHilbert
    globalPairedAbelianPureGhostGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric))

/-- Smooth pure ghost tests lifted into their closed graph Hilbert space. -/
def globalPairedAbelianPureGhostGraphEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    PairedGhost period hPeriod →ₗ[Real]
      GlobalPairedAbelianPureGhostGraphHilbert period hPeriod metric where
  toFun ghost :=
    ⟨globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric ghost,
      (LinearMap.range
        (globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric)
          ghost)⟩
  map_add' first second := Subtype.ext
    ((globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric).map_add
      first second)
  map_smul' scalar ghost := Subtype.ext
    ((globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric).map_smul
      scalar ghost)

theorem globalPairedAbelianPureGhostGraphEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalPairedAbelianPureGhostGraphEmbedding period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion :=
    globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalPairedAbelianPureGhostGraphEmbedding period hPeriod metric) =
        (LinearMap.range inclusion :
          Set (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨ghost, rfl⟩, rfl⟩
      exact ⟨ghost, rfl⟩
    · rintro ⟨ghost, rfl⟩
      exact
        ⟨globalPairedAbelianPureGhostGraphEmbedding period hPeriod metric ghost,
          ⟨ghost, rfl⟩, rfl⟩
  change closure
      (LinearMap.range inclusion :
        Set (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalPairedAbelianPureGhostGraphEmbedding period hPeriod metric))
  rw [hRange]

section AbelianGhostGraphRieszResidual

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

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev GhostGraph :=
  GlobalPairedAbelianPureGhostGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

/-- Continuous Hessian covector restricted to the closed pure-ghost graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GhostGraph period hPeriod configuration data →L[Real] Real :=
  (globalPairedAbelianOffShellHessian period hPeriod
    (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
      hPeriod configuration data analysis chartData state)).comp
        (globalPairedAbelianPureGhostGraphSubmodule period hPeriod
          (BaseMetric period hPeriod configuration data)).subtypeL

/-- Exact Riesz representative of the ghost covector on its closed graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GhostGraph period hPeriod configuration data := by
  letI : CompleteSpace (GhostGraph period hPeriod configuration data) :=
    globalPairedAbelianPureGhostGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  exact
    (InnerProductSpace.toDual Real
      (GhostGraph period hPeriod configuration data)).symm
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphCovector
          period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GhostGraph period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphCovector
        period hPeriod configuration data analysis chartData state test := by
  letI : CompleteSpace (GhostGraph period hPeriod configuration data) :=
    globalPairedAbelianPureGhostGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
  exact InnerProductSpace.toDual_symm_apply

/-- Pair the ghost graph residual with a genuine smooth typed ghost test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing
    (residual : GhostGraph period hPeriod configuration data)
    (test : PairedGhost period hPeriod) : Real :=
  inner Real residual
    (globalPairedAbelianPureGhostGraphEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data) test)

/-- The weak ghost component is exactly represented by its graph-Riesz
residual. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_apply_eq_graphResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PairedGhost period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
        period hPeriod configuration data analysis chartData state test =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual_pairing]
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        (fun sector => ⟨test sector, ⟨0⟩, ⟨0⟩⟩) = _
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphCovector
  simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Smooth test formula for the graph residual. It uses the completed
antighost coordinate paired with the genuine FP image of the test ghost. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing_eq_antighost_fp
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PairedGhost period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test =
      inner Real
        (globalPairedAbelianOffShellAntighostProjection period hPeriod
          (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
            hPeriod configuration data analysis chartData state))
        (globalPairedAbelianFPL2LinearMap period hPeriod
          (BaseMetric period hPeriod configuration data)
          (fun sector => (test sector).field)) := by
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_apply_eq_graphResidualPairing]
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        (fun sector => ⟨test sector, ⟨0⟩, ⟨0⟩⟩) = _
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
  simp only [LinearMap.comp_apply]
  change
    globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (BaseMetric period hPeriod configuration data)
          { potential := 0
            nonminimal := fun sector => ⟨test sector, ⟨0⟩, ⟨0⟩⟩ }) = _
  rw [globalPairedAbelianOffShellHessian_apply]
  simp only [globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellBProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth,
    globalPairedAbelianOffShellFPProjection_smooth,
    map_zero, inner_zero_right, zero_add]
  have hZeroGaugeLieField :
      (fun _ : Sector =>
        (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra)) = 0 := rfl
  rw [hZeroGaugeLieField]
  simp only [map_zero, inner_zero_right, add_zero, zero_add, sub_zero]

/-- Smooth pure ghost tests separate the graph-Riesz residual by construction. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing_separates
    (residual : GhostGraph period hPeriod configuration data) :
    (∀ test : PairedGhost period hPeriod,
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing
          period hPeriod configuration data residual test = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    apply (globalPairedAbelianPureGhostGraphEmbedding_denseRange period hPeriod
      (BaseMetric period hPeriod configuration data)).eq_zero_of_inner_left
        (𝕜 := Real)
    intro test
    exact hPairing test
  · rintro rfl test
    simp [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing]

def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualRepresentation
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
        period hPeriod configuration data analysis chartData state) where
  Residual := GhostGraph period hPeriod configuration data
  zeroResidual := 0
  residual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
      period hPeriod configuration data analysis chartData state
  pairing :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing
      period hPeriod configuration data
  represents := fun test =>
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_apply_eq_graphResidualPairing
      period hPeriod configuration data analysis chartData state test
  separates :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualPairing_separates
      period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
          period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_eq_zero_iff_graphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphResidualRepresentation
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianGhostGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  have hSystem :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  rcases hSystem with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hGhost, _, _⟩
  exact
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_eq_zero_iff_graphResidual
      period hPeriod configuration data analysis chartData state).mp hGhost

/-- Gate 244: the remaining paired Abelian ghost equation has an exact
separating strong residual on the closed Hilbert graph generated by its tests. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_ghost_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_eq_zero_iff_graphResidual
    period hPeriod configuration data analysis chartData state

end AbelianGhostGraphRieszResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D
end JanusFormal
