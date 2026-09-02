import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D

/-!
# Graph-Riesz residual of the diffeomorphism antighost equation

Pure smooth antighost tests generate a closed subspace of the
completed diagonal diffeomorphism graph.  Riesz representation on that
subspace gives an exact separating residual, without asserting a PDE or
`L²` formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D

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
local instance (priority := 11000) alignedRealNontriviallyNormedFieldDiffeomorphismAntighostGraphResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceDiffeomorphismAntighostGraphResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldDiffeomorphismAntighostGraphResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceDiffeomorphismAntighostGraphResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceDiffeomorphismAntighostGraphResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pure antighost inclusion into diagonal nonminimal fields. -/
def globalDiffeomorphismPureAntighostNonminimalLinearMap :
    GlobalDiffeomorphismAntighostField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismNonminimalFields period hPeriod :=
  (globalDiffeomorphismNonminimalFieldsLinearEquiv period hPeriod).symm.toLinearMap.comp
    ((productSecondInclusion
      (GlobalDiffeomorphismGhostField period hPeriod)
      (GlobalDiffeomorphismAntighostField period hPeriod ×
        GlobalDiffeomorphismNakanishiLautrupField period hPeriod)).comp
      (productFirstInclusion
        (GlobalDiffeomorphismAntighostField period hPeriod)
        (GlobalDiffeomorphismNakanishiLautrupField period hPeriod)))

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphNormedAddCommGroupDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphNormedSpaceDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10002) diagonalGraphAddCommGroupDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedAddCommGroupDiffeomorphismAntighostResidual
    period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) diagonalGraphTopologicalSpaceDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedAddCommGroupDiffeomorphismAntighostResidual
    period hPeriod metric).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance (priority := 10001) diagonalGraphContinuousAddDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphModuleDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedSpaceDiffeomorphismAntighostResidual
    period hPeriod metric).toModule

local instance diagonalGraphIsBoundedSMulDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    IsBoundedSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  @NormedSpace.toIsBoundedSMul Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    Real.normedField
    (diagonalGraphNormedAddCommGroupDiffeomorphismAntighostResidual
      period hPeriod metric).toSeminormedAddCommGroup
    (diagonalGraphNormedSpaceDiffeomorphismAntighostResidual
      period hPeriod metric)

local instance diagonalGraphUniformContinuousConstSMulDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    UniformContinuousConstSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  IsBoundedSMul.toUniformContinuousConstSMul

local instance diagonalGraphContinuousConstSMulDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousConstSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  UniformContinuousConstSMul.to_continuousConstSMul Real _

local instance (priority := 10001) diagonalGraphInnerProductSpaceDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphInnerProductSpace
    period hPeriod metric

local instance diagonalGraphCompleteSpaceDiffeomorphismAntighostResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphCompleteSpace
    period hPeriod metric

/-- Pure smooth antighost tests mapped into the completed diagonal graph. -/
def globalDiffeomorphismPureAntighostGraphLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismAntighostField period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric :=
  (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
    period hPeriod metric).comp
    ((globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
      period hPeriod).comp
      (globalDiffeomorphismPureAntighostNonminimalLinearMap
        period hPeriod))

def globalDiffeomorphismPureAntighostGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (LinearMap.range
    (globalDiffeomorphismPureAntighostGraphLinearMap
      period hPeriod metric)).topologicalClosure

abbrev GlobalDiffeomorphismPureAntighostGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismPureAntighostGraphSubmodule
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) pureAntighostGraphNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismAntighostResidual
      period hPeriod metric)
    (diagonalGraphModuleDiffeomorphismAntighostResidual
      period hPeriod metric)
    (globalDiffeomorphismPureAntighostGraphSubmodule
      period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10003) pureAntighostGraphPseudoMetricSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    PseudoMetricSpace
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphNormedAddCommGroup period hPeriod metric).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) pureAntighostGraphUniformSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    UniformSpace
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphPseudoMetricSpace period hPeriod metric).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) pureAntighostGraphSeminormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    SeminormedAddCommGroup
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphNormedAddCommGroup period hPeriod metric).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) pureAntighostGraphAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphNormedAddCommGroup period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) pureAntighostGraphTopologicalSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphUniformSpace period hPeriod metric).toTopologicalSpace

local instance (priority := 10001) pureAntighostGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismAntighostResidual
      period hPeriod metric).toSeminormedAddCommGroup
    (diagonalGraphInnerProductSpaceDiffeomorphismAntighostResidual
      period hPeriod metric)
    (globalDiffeomorphismPureAntighostGraphSubmodule
      period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10001) pureAntighostGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphInnerProductSpace period hPeriod metric).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) pureAntighostGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) :=
  (pureAntighostGraphNormedSpace period hPeriod metric).toModule

@[implicit_reducible]
def globalDiffeomorphismPureAntighostGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric) := by
  unfold GlobalDiffeomorphismPureAntighostGraphHilbert
    globalDiffeomorphismPureAntighostGraphSubmodule
  exact isClosed_closure.completeSpace_coe

def globalDiffeomorphismPureAntighostGraphEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismAntighostField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismPureAntighostGraphHilbert
        period hPeriod metric where
  toFun test :=
    ⟨globalDiffeomorphismPureAntighostGraphLinearMap
        period hPeriod metric test,
      (LinearMap.range
        (globalDiffeomorphismPureAntighostGraphLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalDiffeomorphismPureAntighostGraphLinearMap
            period hPeriod metric) test)⟩
  map_add' first second := Subtype.ext
    ((globalDiffeomorphismPureAntighostGraphLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar test := Subtype.ext
    ((globalDiffeomorphismPureAntighostGraphLinearMap
      period hPeriod metric).map_smul scalar test)

theorem globalDiffeomorphismPureAntighostGraphEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalDiffeomorphismPureAntighostGraphEmbedding
        period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion :=
    globalDiffeomorphismPureAntighostGraphLinearMap
      period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalDiffeomorphismPureAntighostGraphEmbedding
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
        ⟨globalDiffeomorphismPureAntighostGraphEmbedding
            period hPeriod metric test, ⟨test, rfl⟩, rfl⟩
  change closure
      (LinearMap.range inclusion : Set
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalDiffeomorphismPureAntighostGraphEmbedding
        period hPeriod metric))
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

private abbrev AntighostGraph :=
  GlobalDiffeomorphismPureAntighostGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    AntighostGraph period hPeriod configuration data →L[Real] Real :=
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)).comp
    (globalDiffeomorphismPureAntighostGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data)).subtypeL

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    AntighostGraph period hPeriod configuration data := by
  letI : CompleteSpace (AntighostGraph period hPeriod configuration data) :=
    globalDiffeomorphismPureAntighostGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  exact (InnerProductSpace.toDual Real
    (AntighostGraph period hPeriod configuration data)).symm
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphCovector
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : AntighostGraph period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphCovector
        period hPeriod configuration data analysis chartData state test := by
  letI : CompleteSpace (AntighostGraph period hPeriod configuration data) :=
    globalDiffeomorphismPureAntighostGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
  exact InnerProductSpace.toDual_symm_apply

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing
    (residual : AntighostGraph period hPeriod configuration data)
    (test : GlobalDiffeomorphismAntighostField period hPeriod) : Real :=
  inner Real residual
    (globalDiffeomorphismPureAntighostGraphEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data) test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostBRSTCovector_apply_eq_graphResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GlobalDiffeomorphismAntighostField period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
        period hPeriod configuration data analysis chartData state test =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual_pairing]
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        ((globalDiffeomorphismPureAntighostNonminimalLinearMap
          period hPeriod) test) = _
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphCovector
  simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing_separates
    (residual : AntighostGraph period hPeriod configuration data) :
    (∀ test : GlobalDiffeomorphismAntighostField period hPeriod,
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing
          period hPeriod configuration data residual test = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    apply (globalDiffeomorphismPureAntighostGraphEmbedding_denseRange
      period hPeriod (BaseMetric period hPeriod configuration data)
      ).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    exact hPairing test
  · rintro rfl test
    unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing
    exact inner_zero_left _

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualRepresentation
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
        period hPeriod configuration data analysis chartData state) where
  Residual := AntighostGraph period hPeriod configuration data
  zeroResidual := 0
  residual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
      period hPeriod configuration data analysis chartData state
  pairing :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing
      period hPeriod configuration data
  represents := fun test =>
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostBRSTCovector_apply_eq_graphResidualPairing
      period hPeriod configuration data analysis chartData state test
  separates :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualPairing_separates
      period hPeriod configuration data
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostBRSTCovector_eq_zero_iff_graphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphResidualRepresentation
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismAntighostGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  have hSystem :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  rcases hSystem with
    ⟨_, _, _, _, _, _, _, _, hAntighost, _, _, _, _, _⟩
  exact
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostBRSTCovector_eq_zero_iff_graphResidual
      period hPeriod configuration data analysis chartData state).mp
      hAntighost

/-- Gate 246: exact graph-Riesz residual of the diffeomorphism antighost
equation on the closed Hilbert graph generated by its pure tests. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_antighost_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostBRSTCovector_eq_zero_iff_graphResidual
    period hPeriod configuration data analysis chartData state

end Residual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D
end JanusFormal
