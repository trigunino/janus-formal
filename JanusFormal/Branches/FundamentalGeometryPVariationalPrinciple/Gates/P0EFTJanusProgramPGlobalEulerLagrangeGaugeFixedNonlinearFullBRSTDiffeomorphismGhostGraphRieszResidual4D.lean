import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D

/-!
# Graph-Riesz residual of the diffeomorphism ghost equation

Pure smooth ghost tests generate a closed subspace of the completed diagonal
diffeomorphism graph. Riesz representation on that subspace gives an exact
separating residual, without asserting a PDE or `L²` formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D

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
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldDiffeomorphismGhostGraphResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceDiffeomorphismGhostGraphResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldDiffeomorphismGhostGraphResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceDiffeomorphismGhostGraphResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceDiffeomorphismGhostGraphResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pure ghost inclusion into diagonal nonminimal fields. -/
def globalDiffeomorphismPureGhostNonminimalLinearMap :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismNonminimalFields period hPeriod :=
  (globalDiffeomorphismNonminimalFieldsLinearEquiv period hPeriod).symm.toLinearMap.comp
    (productFirstInclusion
      (GlobalDiffeomorphismGhostField period hPeriod)
      (GlobalDiffeomorphismAntighostField period hPeriod ×
        GlobalDiffeomorphismNakanishiLautrupField period hPeriod))

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphNormedSpaceDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10002) diagonalGraphAddCommGroupDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
    period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) diagonalGraphTopologicalSpaceDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
    period hPeriod metric).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance (priority := 10001) diagonalGraphContinuousAddDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphModuleDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedSpaceDiffeomorphismGhostResidual
    period hPeriod metric).toModule

local instance diagonalGraphIsBoundedSMulDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    IsBoundedSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  @NormedSpace.toIsBoundedSMul Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    Real.normedField
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
      period hPeriod metric).toSeminormedAddCommGroup
    (diagonalGraphNormedSpaceDiffeomorphismGhostResidual
      period hPeriod metric)

local instance diagonalGraphUniformContinuousConstSMulDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    UniformContinuousConstSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  IsBoundedSMul.toUniformContinuousConstSMul

local instance diagonalGraphContinuousConstSMulDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousConstSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  UniformContinuousConstSMul.to_continuousConstSMul Real _

local instance (priority := 10001) diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphInnerProductSpace
    period hPeriod metric

local instance diagonalGraphCompleteSpaceDiffeomorphismGhostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphCompleteSpace
    period hPeriod metric

/-- Pure smooth ghost tests mapped into the completed diagonal graph. -/
def globalDiffeomorphismPureGhostGraphLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric :=
  (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
    period hPeriod metric).comp
    ((globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
      period hPeriod).comp
      (globalDiffeomorphismPureGhostNonminimalLinearMap period hPeriod))

def globalDiffeomorphismPureGhostGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (LinearMap.range
    (globalDiffeomorphismPureGhostGraphLinearMap
      period hPeriod metric)).topologicalClosure

abbrev GlobalDiffeomorphismPureGhostGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismPureGhostGraphSubmodule period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) pureGhostGraphNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
      period hPeriod metric)
    (diagonalGraphModuleDiffeomorphismGhostResidual
      period hPeriod metric)
    (globalDiffeomorphismPureGhostGraphSubmodule period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10003) pureGhostGraphPseudoMetricSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    PseudoMetricSpace
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphNormedAddCommGroup period hPeriod metric).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) pureGhostGraphUniformSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    UniformSpace
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphPseudoMetricSpace period hPeriod metric).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) pureGhostGraphSeminormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    SeminormedAddCommGroup
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphNormedAddCommGroup period hPeriod metric).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) pureGhostGraphAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphNormedAddCommGroup period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) pureGhostGraphTopologicalSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphUniformSpace period hPeriod metric).toTopologicalSpace

local instance (priority := 10001) pureGhostGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
      period hPeriod metric).toSeminormedAddCommGroup
    (diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual
      period hPeriod metric)
    (globalDiffeomorphismPureGhostGraphSubmodule period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10001) pureGhostGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphInnerProductSpace period hPeriod metric).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) pureGhostGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) :=
  (pureGhostGraphNormedSpace period hPeriod metric).toModule

@[implicit_reducible]
def globalDiffeomorphismPureGhostGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric) := by
  unfold GlobalDiffeomorphismPureGhostGraphHilbert
    globalDiffeomorphismPureGhostGraphSubmodule
  exact isClosed_closure.completeSpace_coe

def globalDiffeomorphismPureGhostGraphEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod metric where
  toFun test :=
    ⟨globalDiffeomorphismPureGhostGraphLinearMap
        period hPeriod metric test,
      (LinearMap.range
        (globalDiffeomorphismPureGhostGraphLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalDiffeomorphismPureGhostGraphLinearMap
            period hPeriod metric) test)⟩
  map_add' first second := Subtype.ext
    ((globalDiffeomorphismPureGhostGraphLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar test := Subtype.ext
    ((globalDiffeomorphismPureGhostGraphLinearMap
      period hPeriod metric).map_smul scalar test)

theorem globalDiffeomorphismPureGhostGraphEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalDiffeomorphismPureGhostGraphEmbedding period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion :=
    globalDiffeomorphismPureGhostGraphLinearMap period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalDiffeomorphismPureGhostGraphEmbedding
            period hPeriod metric) =
        (LinearMap.range inclusion : Set
          (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
            period hPeriod metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalDiffeomorphismPureGhostGraphEmbedding
            period hPeriod metric test, ⟨test, rfl⟩, rfl⟩
  change closure
      (LinearMap.range inclusion : Set
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalDiffeomorphismPureGhostGraphEmbedding period hPeriod metric))
  rw [hRange]

section Residual

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
  GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GhostGraph period hPeriod configuration data →L[Real] Real :=
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)).comp
    (globalDiffeomorphismPureGhostGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data)).subtypeL

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GhostGraph period hPeriod configuration data := by
  letI : CompleteSpace (GhostGraph period hPeriod configuration data) :=
    globalDiffeomorphismPureGhostGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  exact (InnerProductSpace.toDual Real
    (GhostGraph period hPeriod configuration data)).symm
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphCovector
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GhostGraph period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphCovector
        period hPeriod configuration data analysis chartData state test := by
  letI : CompleteSpace (GhostGraph period hPeriod configuration data) :=
    globalDiffeomorphismPureGhostGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
  exact InnerProductSpace.toDual_symm_apply

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing
    (residual : GhostGraph period hPeriod configuration data)
    (test : GlobalDiffeomorphismGhostField period hPeriod) : Real :=
  inner Real residual
    (globalDiffeomorphismPureGhostGraphEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data) test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostBRSTCovector_apply_eq_graphResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GlobalDiffeomorphismGhostField period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
        period hPeriod configuration data analysis chartData state test =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual_pairing]
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        ((globalDiffeomorphismPureGhostNonminimalLinearMap
          period hPeriod) test) = _
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphCovector
  simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing_separates
    (residual : GhostGraph period hPeriod configuration data) :
    (∀ test : GlobalDiffeomorphismGhostField period hPeriod,
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing
          period hPeriod configuration data residual test = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    apply (globalDiffeomorphismPureGhostGraphEmbedding_denseRange
      period hPeriod (BaseMetric period hPeriod configuration data)
      ).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    exact hPairing test
  · rintro rfl test
    unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing
    exact inner_zero_left _

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualRepresentation
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
        period hPeriod configuration data analysis chartData state) where
  Residual := GhostGraph period hPeriod configuration data
  zeroResidual := 0
  residual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
      period hPeriod configuration data analysis chartData state
  pairing :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing
      period hPeriod configuration data
  represents := fun test =>
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostBRSTCovector_apply_eq_graphResidualPairing
      period hPeriod configuration data analysis chartData state test
  separates :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualPairing_separates
      period hPeriod configuration data
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostBRSTCovector_eq_zero_iff_graphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphResidualRepresentation
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismGhostGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  have hSystem :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  rcases hSystem with
    ⟨_, _, _, _, _, _, _, hGhost, _, _, _, _, _, _⟩
  exact
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostBRSTCovector_eq_zero_iff_graphResidual
      period hPeriod configuration data analysis chartData state).mp hGhost

/-- Gate 248: exact graph-Riesz residual of the diffeomorphism nonminimal ghost
equation on the closed Hilbert graph generated by its pure tests. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_ghost_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostBRSTCovector_eq_zero_iff_graphResidual
    period hPeriod configuration data analysis chartData state

end Residual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
end JanusFormal
