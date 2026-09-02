import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D

/-!
# Graph-Riesz residual of the diffeomorphism Nakanishi--Lautrup equation

Pure smooth Nakanishi--Lautrup tests generate a closed subspace of the
completed diagonal diffeomorphism graph.  Riesz representation on that
subspace gives an exact separating residual, without asserting a PDE or
`L²` formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D

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
local instance (priority := 11000) alignedRealNontriviallyNormedFieldDiffeomorphismNakanishiGraphResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceDiffeomorphismNakanishiGraphResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldDiffeomorphismNakanishiGraphResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceDiffeomorphismNakanishiGraphResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceDiffeomorphismNakanishiGraphResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pure Nakanishi--Lautrup inclusion into diagonal nonminimal fields. -/
def globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismNonminimalFields period hPeriod :=
  (globalDiffeomorphismNonminimalFieldsLinearEquiv period hPeriod).symm.toLinearMap.comp
    ((productSecondInclusion
      (GlobalDiffeomorphismGhostField period hPeriod)
      (GlobalDiffeomorphismAntighostField period hPeriod ×
        GlobalDiffeomorphismNakanishiLautrupField period hPeriod)).comp
      (productSecondInclusion
        (GlobalDiffeomorphismAntighostField period hPeriod)
        (GlobalDiffeomorphismNakanishiLautrupField period hPeriod)))

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphNormedAddCommGroupDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphNormedSpaceDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10002) diagonalGraphAddCommGroupDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedAddCommGroupDiffeomorphismNakanishiResidual
    period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) diagonalGraphTopologicalSpaceDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedAddCommGroupDiffeomorphismNakanishiResidual
    period hPeriod metric).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance (priority := 10001) diagonalGraphContinuousAddDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) diagonalGraphModuleDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (diagonalGraphNormedSpaceDiffeomorphismNakanishiResidual
    period hPeriod metric).toModule

local instance diagonalGraphIsBoundedSMulDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    IsBoundedSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  @NormedSpace.toIsBoundedSMul Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    Real.normedField
    (diagonalGraphNormedAddCommGroupDiffeomorphismNakanishiResidual
      period hPeriod metric).toSeminormedAddCommGroup
    (diagonalGraphNormedSpaceDiffeomorphismNakanishiResidual
      period hPeriod metric)

local instance diagonalGraphUniformContinuousConstSMulDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    UniformContinuousConstSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  IsBoundedSMul.toUniformContinuousConstSMul

local instance diagonalGraphContinuousConstSMulDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousConstSMul Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  UniformContinuousConstSMul.to_continuousConstSMul Real _

local instance (priority := 10001) diagonalGraphInnerProductSpaceDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphInnerProductSpace
    period hPeriod metric

local instance diagonalGraphCompleteSpaceDiffeomorphismNakanishiResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphCompleteSpace
    period hPeriod metric

/-- Pure smooth auxiliary tests mapped into the completed diagonal graph. -/
def globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric :=
  (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
    period hPeriod metric).comp
    ((globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
      period hPeriod).comp
      (globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap
        period hPeriod))

def globalDiffeomorphismPureNakanishiLautrupGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  (LinearMap.range
    (globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
      period hPeriod metric)).topologicalClosure

abbrev GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismPureNakanishiLautrupGraphSubmodule
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) pureNakanishiGraphNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismNakanishiResidual
      period hPeriod metric)
    (diagonalGraphModuleDiffeomorphismNakanishiResidual
      period hPeriod metric)
    (globalDiffeomorphismPureNakanishiLautrupGraphSubmodule
      period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10003) pureNakanishiGraphPseudoMetricSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    PseudoMetricSpace
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphNormedAddCommGroup period hPeriod metric).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) pureNakanishiGraphUniformSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    UniformSpace
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphPseudoMetricSpace period hPeriod metric).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) pureNakanishiGraphSeminormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    SeminormedAddCommGroup
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphNormedAddCommGroup period hPeriod metric).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) pureNakanishiGraphAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AddCommGroup
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphNormedAddCommGroup period hPeriod metric).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) pureNakanishiGraphTopologicalSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphUniformSpace period hPeriod metric).toTopologicalSpace

local instance (priority := 10001) pureNakanishiGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphNormedAddCommGroupDiffeomorphismNakanishiResidual
      period hPeriod metric).toSeminormedAddCommGroup
    (diagonalGraphInnerProductSpaceDiffeomorphismNakanishiResidual
      period hPeriod metric)
    (globalDiffeomorphismPureNakanishiLautrupGraphSubmodule
      period hPeriod metric)

@[implicit_reducible]
local instance (priority := 10001) pureNakanishiGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphInnerProductSpace period hPeriod metric).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) pureNakanishiGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) :=
  (pureNakanishiGraphNormedSpace period hPeriod metric).toModule

@[implicit_reducible]
def globalDiffeomorphismPureNakanishiLautrupGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric) := by
  unfold GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
    globalDiffeomorphismPureNakanishiLautrupGraphSubmodule
  exact isClosed_closure.completeSpace_coe

def globalDiffeomorphismPureNakanishiLautrupGraphEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert
        period hPeriod metric where
  toFun test :=
    ⟨globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
        period hPeriod metric test,
      (LinearMap.range
        (globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
            period hPeriod metric) test)⟩
  map_add' first second := Subtype.ext
    ((globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar test := Subtype.ext
    ((globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
      period hPeriod metric).map_smul scalar test)

theorem globalDiffeomorphismPureNakanishiLautrupGraphEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding
        period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion :=
    globalDiffeomorphismPureNakanishiLautrupGraphLinearMap
      period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding
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
        ⟨globalDiffeomorphismPureNakanishiLautrupGraphEmbedding
            period hPeriod metric test, ⟨test, rfl⟩, rfl⟩
  change closure
      (LinearMap.range inclusion : Set
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding
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

private abbrev NakanishiGraph :=
  GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NakanishiGraph period hPeriod configuration data →L[Real] Real :=
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)).comp
    (globalDiffeomorphismPureNakanishiLautrupGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data)).subtypeL

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NakanishiGraph period hPeriod configuration data := by
  letI : CompleteSpace (NakanishiGraph period hPeriod configuration data) :=
    globalDiffeomorphismPureNakanishiLautrupGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  exact (InnerProductSpace.toDual Real
    (NakanishiGraph period hPeriod configuration data)).symm
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphCovector
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : NakanishiGraph period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphCovector
        period hPeriod configuration data analysis chartData state test := by
  letI : CompleteSpace (NakanishiGraph period hPeriod configuration data) :=
    globalDiffeomorphismPureNakanishiLautrupGraphCompleteSpace period hPeriod
      (BaseMetric period hPeriod configuration data)
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
  exact InnerProductSpace.toDual_symm_apply

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing
    (residual : NakanishiGraph period hPeriod configuration data)
    (test : GlobalDiffeomorphismNakanishiLautrupField period hPeriod) : Real :=
  inner Real residual
    (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding period hPeriod
      (BaseMetric period hPeriod configuration data) test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupBRSTCovector_apply_eq_graphResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GlobalDiffeomorphismNakanishiLautrupField period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
        period hPeriod configuration data analysis chartData state test =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
          period hPeriod configuration data analysis chartData state) test := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual_pairing]
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        ((globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap
          period hPeriod) test) = _
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphCovector
  simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing_separates
    (residual : NakanishiGraph period hPeriod configuration data) :
    (∀ test : GlobalDiffeomorphismNakanishiLautrupField period hPeriod,
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing
          period hPeriod configuration data residual test = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    apply (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding_denseRange
      period hPeriod (BaseMetric period hPeriod configuration data)
      ).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    exact hPairing test
  · rintro rfl test
    unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing
    exact inner_zero_left _

def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualRepresentation
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
        period hPeriod configuration data analysis chartData state) where
  Residual := NakanishiGraph period hPeriod configuration data
  zeroResidual := 0
  residual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
      period hPeriod configuration data analysis chartData state
  pairing :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing
      period hPeriod configuration data
  represents := fun test =>
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupBRSTCovector_apply_eq_graphResidualPairing
      period hPeriod configuration data analysis chartData state test
  separates :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualPairing_separates
      period hPeriod configuration data
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
        period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupBRSTCovector_eq_zero_iff_graphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphResidualRepresentation
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismNakanishiLautrupGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  have hSystem :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  rcases hSystem with
    ⟨_, _, _, _, _, _, _, _, _, hNakanishiLautrup, _, _, _, _⟩
  exact
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupBRSTCovector_eq_zero_iff_graphResidual
      period hPeriod configuration data analysis chartData state).mp
      hNakanishiLautrup

/-- Gate 246: exact graph-Riesz residual of the diffeomorphism auxiliary
equation on the closed Hilbert graph generated by its pure tests. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_nakanishiLautrup_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupBRSTCovector_eq_zero_iff_graphResidual
    period hPeriod configuration data analysis chartData state

end Residual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D
end JanusFormal
