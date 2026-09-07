import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongSameActionChartData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

/-! # Same-action chart with a shared diffeomorphism BRST metric

The weak C² datum supplies the physical norm, local action and domain.  Its
canonical tangent equivalence constructs the shared metric graph directly.
Only the existing diffeomorphism gauge-fixing action is added; no quadratic
identity for the matter or LL action is required.
-/

namespace JanusFormal
namespace P0EFTJanusSameActionDiffeomorphismBRSTGraphChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusPairedStrongSameActionChartData4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedField :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

@[implicit_reducible]
local instance (priority := 10001) sameActionGraphNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

local instance (priority := 10001) sameActionGraphContinuousAdd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) sameActionGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

local instance (priority := 10001) sameActionGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphModule
    period hPeriod metric

section SharedMetricChart

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalSameActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev MinimalChart :=
  chartData.toLocalVariationalChart period hPeriod configuration data analysis

/-- The underlying tangent is unchanged; its algebra is transported through
the two compatibility fields of the same-action datum. -/
def sameActionDiffeomorphismTangentEquiv :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical ≃ₗ[Real]
      (MinimalChart period hPeriod configuration data analysis chartData).Model where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' first second := by
    change @Add.add _
        (Submodule.addCommGroup
          (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)).toAdd
        first second =
      @Add.add _ chartData.normedAddCommGroup.toAdd first second
    rw [chartData.toAddCommGroup_eq]
  map_smul' scalar direction := by
    change @SMul.smul Real _
        (Submodule.smul
          (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical))
        scalar direction =
      @SMul.smul Real _ chartData.normedSpace.toModule.toSMul scalar direction
    rw [chartData.toSMul_eq]

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev DiffeomorphismGraph :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev AugmentedAmbient :=
  (MinimalChart period hPeriod configuration data analysis chartData).Model ×
    DiffeomorphismGraph period hPeriod configuration data

local instance (priority := 10002) sameActionAugmentedAmbientModule :
    Module Real
      (AugmentedAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

/-- The existing algebraic core has one physical tangent and one triplet. -/
abbrev SameActionDiffeomorphismCore :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D
    period hPeriod configuration

/-- Reuse the concrete BRST state with the physical tangent's metric slot. -/
abbrev sameActionDiffeomorphismStateLinearMap :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
    period hPeriod configuration

/-- Shared-metric realization in the physical-model/BRST-graph product. -/
def sameActionDiffeomorphismSharedLinearMap :
    SameActionDiffeomorphismCore period hPeriod
        configuration →ₗ[Real]
      AugmentedAmbient period hPeriod configuration data analysis chartData where
  toFun core :=
    ((sameActionDiffeomorphismTangentEquiv period hPeriod
        configuration data analysis chartData) core.1,
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)
        (sameActionDiffeomorphismStateLinearMap
          period hPeriod configuration core))
  map_add' first second := by
    apply Prod.ext
    · exact (sameActionDiffeomorphismTangentEquiv period hPeriod
        configuration data analysis chartData).map_add first.1 second.1
    · exact (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)).map_add
          (sameActionDiffeomorphismStateLinearMap
            period hPeriod configuration first)
          (sameActionDiffeomorphismStateLinearMap
            period hPeriod configuration second)
  map_smul' scalar core := by
    apply Prod.ext
    · exact (sameActionDiffeomorphismTangentEquiv period hPeriod
        configuration data analysis chartData).map_smul scalar core.1
    · exact (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)).map_smul scalar
          (sameActionDiffeomorphismStateLinearMap
            period hPeriod configuration core)

theorem sameActionDiffeomorphismSharedLinearMap_injective :
    Function.Injective
      (sameActionDiffeomorphismSharedLinearMap
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply Prod.ext
  · have hFirst :
        (sameActionDiffeomorphismTangentEquiv period hPeriod
            configuration data analysis chartData) first.1 =
          (sameActionDiffeomorphismTangentEquiv period hPeriod
            configuration data analysis chartData) second.1 :=
      congrArg
        (fun value : AugmentedAmbient period hPeriod configuration data
            analysis chartData ↦ value.1) hEqual
    exact (sameActionDiffeomorphismTangentEquiv period hPeriod
      configuration data analysis chartData).injective hFirst
  · have hGraph := congrArg
      (fun value : AugmentedAmbient period hPeriod configuration data
          analysis chartData ↦ value.2) hEqual
    have hState :=
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
        period hPeriod (BaseMetric period hPeriod configuration data) hGraph
    exact congrArg
      (fun state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ↦
        state.nonminimal) hState

/-- Linear relation enforcing equality of the physical and BRST metric
coordinates. -/
def sameActionDiffeomorphismGraphSubmodule :
    Submodule Real
      (AugmentedAmbient period hPeriod configuration data analysis chartData) :=
  LinearMap.range
    (sameActionDiffeomorphismSharedLinearMap
      period hPeriod configuration data analysis chartData)

/-- Relational chart model with one shared metric coordinate. -/
abbrev SameActionDiffeomorphismGraphChart :=
  sameActionDiffeomorphismGraphSubmodule
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002)
    sameActionBRSTGraphChartNormedAddCommGroup :
    NormedAddCommGroup
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (AugmentedAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (sameActionAugmentedAmbientModule period hPeriod (measure := measure)
      configuration data analysis chartData)
    (sameActionDiffeomorphismGraphSubmodule
      period hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) sameActionBRSTGraphChartNormedSpace :
    NormedSpace Real
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) :=
  Submodule.normedSpace
    (sameActionDiffeomorphismGraphSubmodule
      period hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) sameActionBRSTGraphChartAddCommGroup :
    AddCommGroup
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) :=
  (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
    configuration data analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) sameActionBRSTGraphChartTopologicalSpace :
    TopologicalSpace
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) :=
  (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
    configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10003) sameActionBRSTGraphChartModule :
    Module Real
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) :=
  (sameActionBRSTGraphChartNormedSpace period hPeriod configuration data
    analysis chartData).toModule

/-- The smooth core realizes every point of the shared metric graph. -/
def sameActionDiffeomorphismCoreEmbedding :
    SameActionDiffeomorphismCore period hPeriod
        configuration →ₗ[Real]
      SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData where
  toFun core :=
    ⟨sameActionDiffeomorphismSharedLinearMap
        period hPeriod configuration data analysis chartData core,
      LinearMap.mem_range_self
        (sameActionDiffeomorphismSharedLinearMap
          period hPeriod configuration data analysis chartData) core⟩
  map_add' first second := Subtype.ext
    ((sameActionDiffeomorphismSharedLinearMap
      period hPeriod configuration data analysis chartData).map_add first second)
  map_smul' scalar core := Subtype.ext
    ((sameActionDiffeomorphismSharedLinearMap
      period hPeriod configuration data analysis chartData).map_smul scalar core)

theorem sameActionDiffeomorphismCoreEmbedding_injective :
    Function.Injective
      (sameActionDiffeomorphismCoreEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply sameActionDiffeomorphismSharedLinearMap_injective
    period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

theorem sameActionDiffeomorphismCoreEmbedding_surjective :
    Function.Surjective
      (sameActionDiffeomorphismCoreEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro state
  rcases state.2 with ⟨core, hCore⟩
  exact ⟨core, Subtype.ext hCore⟩

/-- Continuous projection to the exact nonlinear physical chart. -/
def sameActionDiffeomorphismPhysicalProjection :
    SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData →L[Real]
      (MinimalChart period hPeriod configuration data analysis chartData).Model :=
  (ContinuousLinearMap.fst Real
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (DiffeomorphismGraph period hPeriod configuration data)).comp
    (sameActionDiffeomorphismGraphSubmodule
      period hPeriod configuration data analysis chartData).subtypeL

/-- Continuous projection to the completed diffeomorphism BRST graph. -/
def sameActionDiffeomorphismGraphProjection :
    SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData →L[Real]
      DiffeomorphismGraph period hPeriod configuration data :=
  (ContinuousLinearMap.snd Real
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (DiffeomorphismGraph period hPeriod configuration data)).comp
    (sameActionDiffeomorphismGraphSubmodule
      period hPeriod configuration data analysis chartData).subtypeL

@[simp]
theorem sameActionDiffeomorphismPhysicalProjection_core
    (core : SameActionDiffeomorphismCore
      period hPeriod configuration) :
    sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData
        (sameActionDiffeomorphismCoreEmbedding
          period hPeriod configuration data analysis chartData core) =
      (sameActionDiffeomorphismTangentEquiv period hPeriod
        configuration data analysis chartData) core.1 :=
  rfl

@[simp]
theorem sameActionDiffeomorphismGraphProjection_core
    (core : SameActionDiffeomorphismCore
      period hPeriod configuration) :
    sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData
        (sameActionDiffeomorphismCoreEmbedding
          period hPeriod configuration data analysis chartData core) =
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)
        (sameActionDiffeomorphismStateLinearMap
          period hPeriod configuration core) :=
  rfl

/-- Admissible nonlinear domain; BRST graph coordinates impose no additional
local restriction. -/
def sameActionDiffeomorphismDomain :
    Set
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) :=
  sameActionDiffeomorphismPhysicalProjection
      period hPeriod configuration data analysis chartData ⁻¹'
    (MinimalChart period hPeriod configuration data analysis chartData).family.domain

theorem sameActionDiffeomorphismDomain_isOpen :
    IsOpen
      (sameActionDiffeomorphismDomain period hPeriod
        configuration data analysis chartData) :=
  (MinimalChart period hPeriod configuration data analysis chartData).isOpen_domain.preimage
    (sameActionDiffeomorphismPhysicalProjection
      period hPeriod configuration data analysis chartData).continuous

theorem sameActionDiffeomorphismDomain_zero_mem :
    (0 : SameActionDiffeomorphismGraphChart
      period hPeriod configuration data analysis chartData) ∈
      sameActionDiffeomorphismDomain period hPeriod
        configuration data analysis chartData := by
  change
    sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData 0 ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain
  rw [map_zero]
  exact (MinimalChart period hPeriod configuration data analysis chartData).zero_mem_domain

/-- Exact nonlinear physical action plus the diagonal diffeomorphism BRST
gauge-fixing action on the shared-metric graph. -/
def sameActionDiffeomorphismAction
    (state : SameActionDiffeomorphismGraphChart
      period hPeriod configuration data analysis chartData) : Real :=
  globalCandidateALocalActionPullback period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData state) +
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
      couplings (BaseMetric period hPeriod configuration data)
      (sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData state)

/-- Exact first variation on the nonlinear shared-metric chart. -/
def sameActionDiffeomorphismEulerOperator
    (state : SameActionDiffeomorphismGraphChart
      period hPeriod configuration data analysis chartData) :
    SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData →L[Real] Real :=
  (globalCandidateALocalEulerLagrangeOperator period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData state)).comp
    (sameActionDiffeomorphismPhysicalProjection
      period hPeriod configuration data analysis chartData) +
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
      couplings (BaseMetric period hPeriod configuration data)
      (sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData state)).comp
    (sameActionDiffeomorphismGraphProjection
      period hPeriod configuration data analysis chartData)

theorem sameActionDiffeomorphismAction_hasFDerivAt
    (state : SameActionDiffeomorphismGraphChart
      period hPeriod configuration data analysis chartData)
    (hState : state ∈
      sameActionDiffeomorphismDomain period hPeriod
        configuration data analysis chartData) :
    @HasFDerivAt Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData).toAddCommGroup
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData).toModule
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      Real
      (inferInstance : NormedAddCommGroup Real).toAddCommGroup
      (inferInstance : NormedSpace Real Real).toModule
      (inferInstance : NormedAddCommGroup Real).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (sameActionDiffeomorphismAction period
        hPeriod configuration data analysis chartData)
      (sameActionDiffeomorphismEulerOperator period
        hPeriod configuration data analysis chartData state) state := by
  change
    sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData state ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain
    at hState
  have hPhysical :=
    @HasFDerivAt.comp Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedAddCommGroup
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedSpace
      Real inferInstance inferInstance
      (sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData)
      (sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData)
      state
      (globalCandidateALocalActionPullback period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData))
      (globalCandidateALocalEulerLagrangeOperator period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData)
        (sameActionDiffeomorphismPhysicalProjection
          period hPeriod configuration data analysis chartData state))
      (globalCandidateALocalAction_hasFDerivAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData)
        (sameActionDiffeomorphismPhysicalProjection
          period hPeriod configuration data analysis chartData state) hState)
      (@ContinuousLinearMap.hasFDerivAt Real alignedRealNontriviallyNormedField
        (SameActionDiffeomorphismGraphChart
          period hPeriod configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toAddCommGroup
        (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData).toModule
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (MinimalChart period hPeriod configuration data analysis chartData).Model
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup.toAddCommGroup
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedSpace.toModule
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (sameActionDiffeomorphismPhysicalProjection
          period hPeriod configuration data analysis chartData) state)
  have hBRST :=
    @HasFDerivAt.comp Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (DiffeomorphismGraph period hPeriod configuration data)
      (sameActionGraphNormedAddCommGroup period hPeriod
        (BaseMetric period hPeriod configuration data))
      (sameActionGraphNormedSpace period hPeriod
        (BaseMetric period hPeriod configuration data))
      Real inferInstance inferInstance
      (sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData)
      (sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData)
      state
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
        couplings (BaseMetric period hPeriod configuration data))
      (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings (BaseMetric period hPeriod configuration data)
        (sameActionDiffeomorphismGraphProjection
          period hPeriod configuration data analysis chartData state))
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction_hasFDerivAt
        period hPeriod couplings (BaseMetric period hPeriod configuration data)
        (sameActionDiffeomorphismGraphProjection
          period hPeriod configuration data analysis chartData state))
      (@ContinuousLinearMap.hasFDerivAt Real alignedRealNontriviallyNormedField
        (SameActionDiffeomorphismGraphChart
          period hPeriod configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toAddCommGroup
        (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData).toModule
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (DiffeomorphismGraph period hPeriod configuration data)
        (sameActionGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data)).toAddCommGroup
        (sameActionGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data)).toModule
        (sameActionGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (sameActionDiffeomorphismGraphProjection
          period hPeriod configuration data analysis chartData) state)
  have hSum :=
    @HasFDerivAt.add Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance _ _ _ _ state hPhysical hBRST
  convert hSum using 1
  all_goals rfl

theorem sameActionDiffeomorphismAction_contDiffAt_two
    (state : SameActionDiffeomorphismGraphChart
      period hPeriod configuration data analysis chartData)
    (hState : state ∈
      sameActionDiffeomorphismDomain period hPeriod
        configuration data analysis chartData) :
    @ContDiffAt Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance 2
      (sameActionDiffeomorphismAction period
        hPeriod configuration data analysis chartData) state := by
  change
    sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData state ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain
    at hState
  have hPhysicalProjection :
      @ContDiffAt Real alignedRealNontriviallyNormedField
        (SameActionDiffeomorphismGraphChart
          period hPeriod configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (MinimalChart period hPeriod configuration data analysis chartData).Model
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedSpace
        2
        (sameActionDiffeomorphismPhysicalProjection
          period hPeriod configuration data analysis chartData) state :=
    @ContDiff.contDiffAt Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedAddCommGroup
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedSpace
      (sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData)
      state 2
      (@ContinuousLinearMap.contDiff Real
        (SameActionDiffeomorphismGraphChart
          period hPeriod configuration data analysis chartData)
        (MinimalChart period hPeriod configuration data analysis chartData).Model
        alignedRealNontriviallyNormedField
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedSpace
        2
        (sameActionDiffeomorphismPhysicalProjection
          period hPeriod configuration data analysis chartData))
  have hGraphProjection :
      @ContDiffAt Real alignedRealNontriviallyNormedField
        (SameActionDiffeomorphismGraphChart
          period hPeriod configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (DiffeomorphismGraph period hPeriod configuration data)
        (sameActionGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (sameActionGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        2
        (sameActionDiffeomorphismGraphProjection
          period hPeriod configuration data analysis chartData) state :=
    @ContDiff.contDiffAt Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (DiffeomorphismGraph period hPeriod configuration data)
      (sameActionGraphNormedAddCommGroup period hPeriod
        (BaseMetric period hPeriod configuration data))
      (sameActionGraphNormedSpace period hPeriod
        (BaseMetric period hPeriod configuration data))
      (sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData)
      state 2
      (@ContinuousLinearMap.contDiff Real
        (SameActionDiffeomorphismGraphChart
          period hPeriod configuration data analysis chartData)
        (DiffeomorphismGraph period hPeriod configuration data)
        alignedRealNontriviallyNormedField
        (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (sameActionGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (sameActionGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        2
        (sameActionDiffeomorphismGraphProjection
          period hPeriod configuration data analysis chartData))
  have hPhysical :=
    @ContDiffAt.comp Real
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      Real alignedRealNontriviallyNormedField
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedAddCommGroup
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedSpace
      inferInstance inferInstance
      (sameActionDiffeomorphismPhysicalProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateALocalActionPullback period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData))
      2
      state
      (globalCandidateALocalActionPullback_contDiffAt_two period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData)
        (sameActionDiffeomorphismPhysicalProjection
          period hPeriod configuration data analysis chartData state) hState)
      hPhysicalProjection
  have hBRST :=
    @ContDiffAt.comp Real
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (DiffeomorphismGraph period hPeriod configuration data)
      Real alignedRealNontriviallyNormedField
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (sameActionGraphNormedAddCommGroup period hPeriod
        (BaseMetric period hPeriod configuration data))
      (sameActionGraphNormedSpace period hPeriod
        (BaseMetric period hPeriod configuration data))
      inferInstance inferInstance
      (sameActionDiffeomorphismGraphProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
        couplings (BaseMetric period hPeriod configuration data))
      2
      state
      (@ContDiff.contDiffAt Real alignedRealNontriviallyNormedField
        (DiffeomorphismGraph period hPeriod configuration data)
        (sameActionGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (sameActionGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        Real inferInstance inferInstance
        (globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
          couplings (BaseMetric period hPeriod configuration data))
        (sameActionDiffeomorphismGraphProjection
          period hPeriod configuration data analysis chartData state)
        2
        (globalCandidateADiagonalDiffeomorphismOffShellGraphAction_contDiff_two
          period hPeriod couplings
          (BaseMetric period hPeriod configuration data)))
      hGraphProjection
  have hSum :=
    @ContDiffAt.add Real alignedRealNontriviallyNormedField
      (SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (sameActionBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance state 2 _ _ hPhysical hBRST
  convert hSum using 1
  all_goals rfl

/-- On the canonical core the action is exactly the nonlinear covariant action
plus the genuine diffeomorphism gauge-fermion BRST variation. -/
theorem sameActionDiffeomorphismAction_core_eq
    (core : SameActionDiffeomorphismCore
      period hPeriod configuration)
    (hCore :
      (sameActionDiffeomorphismTangentEquiv period hPeriod
          configuration data analysis chartData) core.1 ∈
        (MinimalChart period hPeriod configuration data analysis chartData).family.domain) :
    sameActionDiffeomorphismAction period hPeriod
        configuration data analysis chartData
        (sameActionDiffeomorphismCoreEmbedding
          period hPeriod configuration data analysis chartData core) =
      globalCandidateACovariantAction period hPeriod
          ((MinimalChart period hPeriod configuration data analysis chartData).family.datumAt
            ((sameActionDiffeomorphismTangentEquiv period hPeriod
              configuration data analysis chartData) core.1) hCore).2 measure +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
          period hPeriod couplings (BaseMetric period hPeriod configuration data)
          (sameActionDiffeomorphismStateLinearMap
            period hPeriod configuration core) := by
  unfold sameActionDiffeomorphismAction
  rw [sameActionDiffeomorphismPhysicalProjection_core,
    sameActionDiffeomorphismGraphProjection_core,
    globalCandidateALocalActionPullback_eq_covariant_of_mem period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      _ hCore,
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction_smooth_eq_BRST]

/-- Gate 628: the exact nonlinear physical chart and the completed diagonal
diffeomorphism graph form one faithful shared-metric relational chart. -/
theorem same_action_diffeomorphism_BRST_graph_chart_gate :
    IsOpen
        (sameActionDiffeomorphismDomain period hPeriod
          configuration data analysis chartData) ∧
      (0 : SameActionDiffeomorphismGraphChart
        period hPeriod configuration data analysis chartData) ∈
          sameActionDiffeomorphismDomain period hPeriod
            configuration data analysis chartData ∧
      Function.Bijective
        (sameActionDiffeomorphismCoreEmbedding
          period hPeriod configuration data analysis chartData) := by
  exact ⟨sameActionDiffeomorphismDomain_isOpen
      period hPeriod configuration data analysis chartData,
    sameActionDiffeomorphismDomain_zero_mem
      period hPeriod configuration data analysis chartData,
    sameActionDiffeomorphismCoreEmbedding_injective
      period hPeriod configuration data analysis chartData,
    sameActionDiffeomorphismCoreEmbedding_surjective
      period hPeriod configuration data analysis chartData⟩

end SharedMetricChart

end
end P0EFTJanusSameActionDiffeomorphismBRSTGraphChart4D
end JanusFormal

