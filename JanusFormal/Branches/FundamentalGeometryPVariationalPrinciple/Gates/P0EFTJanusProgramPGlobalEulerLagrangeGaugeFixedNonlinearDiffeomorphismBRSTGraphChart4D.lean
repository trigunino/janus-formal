import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D

/-!
# Nonlinear physical chart with a shared-metric diffeomorphism BRST graph

This gate couples the exact nonlinear minimal-physical local action to the
existing diagonal diffeomorphism BRST graph.  The graph metric perturbation is
extracted from the same physical tangent, so no metric degree of freedom is
duplicated.  The resulting relational chart is the range inside the product
of the physical chart and the completed BRST graph.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 3600000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D

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
local instance (priority := 10001) nonlinearGraphNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

local instance (priority := 10001) nonlinearGraphContinuousAdd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

@[implicit_reducible]
local instance (priority := 10001) nonlinearGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

local instance (priority := 10001) nonlinearGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphModule
    period hPeriod metric

local instance (priority := 10001) nonlinearGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphInnerProductSpace
    period hPeriod metric

local instance (priority := 10001) nonlinearGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphCompleteSpace
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
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev DiffeomorphismGraph :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev AugmentedAmbient :=
  (MinimalChart period hPeriod configuration data analysis chartData).Model ×
    DiffeomorphismGraph period hPeriod configuration data

local instance (priority := 10002) nonlinearAugmentedAmbientModule :
    Module Real
      (AugmentedAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

/-- Algebraic smooth core: a corrected physical tangent and one shared
diffeomorphism `c/cbar/B` triplet. -/
abbrev GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical ×
    GlobalDiffeomorphismNonminimalFields period hPeriod

/-- The BRST state uses exactly the metric component of the physical tangent. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun core :=
    { metricPerturbation :=
        core.1.1.completeVariation.fullMetricPerturbation
      nonminimal := core.2 }
  map_add' first second := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · rfl
    · rfl
  map_smul' scalar core := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · rfl
    · rfl

/-- Shared-metric realization in the physical-model/BRST-graph product. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      AugmentedAmbient period hPeriod configuration data analysis chartData where
  toFun core :=
    ((globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
        configuration data analysis chartData) core.1,
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
          period hPeriod configuration core))
  map_add' first second := by
    apply Prod.ext
    · exact (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
        configuration data analysis chartData).map_add first.1 second.1
    · exact (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)).map_add
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
            period hPeriod configuration first)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
            period hPeriod configuration second)
  map_smul' scalar core := by
    apply Prod.ext
    · exact (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
        configuration data analysis chartData).map_smul scalar core.1
    · exact (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)).map_smul scalar
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
            period hPeriod configuration core)

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply Prod.ext
  · have hFirst :
        (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
            configuration data analysis chartData) first.1 =
          (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
            configuration data analysis chartData) second.1 :=
      congrArg
        (fun value : AugmentedAmbient period hPeriod configuration data
            analysis chartData ↦ value.1) hEqual
    exact (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
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
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphSubmodule4D :
    Submodule Real
      (AugmentedAmbient period hPeriod configuration data analysis chartData) :=
  LinearMap.range
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap
      period hPeriod configuration data analysis chartData)

/-- Relational chart model with one shared metric coordinate. -/
abbrev GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D :=
  globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphSubmodule4D
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002)
    nonlinearBRSTGraphChartNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (AugmentedAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (nonlinearAugmentedAmbientModule period hPeriod (measure := measure)
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphSubmodule4D
      period hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) nonlinearBRSTGraphChartNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) :=
  Submodule.normedSpace
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphSubmodule4D
      period hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) nonlinearBRSTGraphChartAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) :=
  (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
    configuration data analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) nonlinearBRSTGraphChartTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) :=
  (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
    configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10003) nonlinearBRSTGraphChartModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) :=
  (nonlinearBRSTGraphChartNormedSpace period hPeriod configuration data
    analysis chartData).toModule

/-- Canonical dense/smooth realization in the relational chart. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData where
  toFun core :=
    ⟨globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap
        period hPeriod configuration data analysis chartData core,
      LinearMap.mem_range_self
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap
          period hPeriod configuration data analysis chartData) core⟩
  map_add' first second := Subtype.ext
    ((globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap
      period hPeriod configuration data analysis chartData).map_add first second)
  map_smul' scalar core := Subtype.ext
    ((globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap
      period hPeriod configuration data analysis chartData).map_smul scalar core)

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTSharedLinearMap_injective
    period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_surjective :
    Function.Surjective
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro state
  rcases state.2 with ⟨core, hCore⟩
  exact ⟨core, Subtype.ext hCore⟩

/-- Algebraic equivalence with the faithful smooth core.  No topological
completeness claim is made for the relational range. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEquiv :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D period hPeriod
        configuration ≃ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData :=
  LinearEquiv.ofBijective
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
      period hPeriod configuration data analysis chartData)
    ⟨globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_injective
        period hPeriod configuration data analysis chartData,
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_surjective
        period hPeriod configuration data analysis chartData⟩

/-- Continuous projection to the exact nonlinear physical chart. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData →L[Real]
      (MinimalChart period hPeriod configuration data analysis chartData).Model :=
  (ContinuousLinearMap.fst Real
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (DiffeomorphismGraph period hPeriod configuration data)).comp
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphSubmodule4D
      period hPeriod configuration data analysis chartData).subtypeL

/-- Continuous projection to the completed diffeomorphism BRST graph. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData →L[Real]
      DiffeomorphismGraph period hPeriod configuration data :=
  (ContinuousLinearMap.snd Real
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (DiffeomorphismGraph period hPeriod configuration data)).comp
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphSubmodule4D
      period hPeriod configuration data analysis chartData).subtypeL

@[simp]
theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection_core
    (core : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D
      period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData core) =
      (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
        configuration data analysis chartData) core.1 :=
  rfl

@[simp]
theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection_core
    (core : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D
      period hPeriod configuration) :
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData core) =
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
          period hPeriod configuration core) :=
  rfl

/-- Admissible nonlinear domain; BRST graph coordinates impose no additional
local restriction. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain :
    Set
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
      period hPeriod configuration data analysis chartData ⁻¹'
    (MinimalChart period hPeriod configuration data analysis chartData).family.domain

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain_isOpen :
    IsOpen
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData) :=
  (MinimalChart period hPeriod configuration data analysis chartData).isOpen_domain.preimage
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
      period hPeriod configuration data analysis chartData).continuous

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain_zero_mem :
    (0 : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
      period hPeriod configuration data analysis chartData) ∈
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData := by
  change
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData 0 ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain
  rw [map_zero]
  exact (MinimalChart period hPeriod configuration data analysis chartData).zero_mem_domain

/-- Exact nonlinear physical action plus the diagonal diffeomorphism BRST
gauge-fixing action on the shared-metric graph. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction
    (state : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
      period hPeriod configuration data analysis chartData) : Real :=
  globalCandidateALocalActionPullback period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData state) +
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
      couplings (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData state)

/-- Exact first variation on the nonlinear shared-metric chart. -/
def globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTEulerOperator
    (state : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
      period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData →L[Real] Real :=
  (globalCandidateALocalEulerLagrangeOperator period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData state)).comp
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
      period hPeriod configuration data analysis chartData) +
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
      couplings (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData state)).comp
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
      period hPeriod configuration data analysis chartData)

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_hasFDerivAt
    (state : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
      period hPeriod configuration data analysis chartData)
    (hState : state ∈
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData) :
    @HasFDerivAt Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData).toAddCommGroup
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData).toModule
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      Real
      (inferInstance : NormedAddCommGroup Real).toAddCommGroup
      (inferInstance : NormedSpace Real Real).toModule
      (inferInstance : NormedAddCommGroup Real).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period
        hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTEulerOperator period
        hPeriod configuration data analysis chartData state) state := by
  change
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData state ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain
    at hState
  have hPhysical :=
    @HasFDerivAt.comp Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedAddCommGroup
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedSpace
      Real inferInstance inferInstance
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData)
      state
      (globalCandidateALocalActionPullback period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData))
      (globalCandidateALocalEulerLagrangeOperator period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData state))
      (globalCandidateALocalAction_hasFDerivAt period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData state) hState)
      (@ContinuousLinearMap.hasFDerivAt Real alignedRealNontriviallyNormedField
        (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
          period hPeriod configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toAddCommGroup
        (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData).toModule
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (MinimalChart period hPeriod configuration data analysis chartData).Model
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup.toAddCommGroup
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedSpace.toModule
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData) state)
  have hBRST :=
    @HasFDerivAt.comp Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (DiffeomorphismGraph period hPeriod configuration data)
      (nonlinearGraphNormedAddCommGroup period hPeriod
        (BaseMetric period hPeriod configuration data))
      (nonlinearGraphNormedSpace period hPeriod
        (BaseMetric period hPeriod configuration data))
      Real inferInstance inferInstance
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData)
      state
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
        couplings (BaseMetric period hPeriod configuration data))
      (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData state))
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction_hasFDerivAt
        period hPeriod couplings (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData state))
      (@ContinuousLinearMap.hasFDerivAt Real alignedRealNontriviallyNormedField
        (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
          period hPeriod configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toAddCommGroup
        (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData).toModule
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (DiffeomorphismGraph period hPeriod configuration data)
        (nonlinearGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data)).toAddCommGroup
        (nonlinearGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data)).toModule
        (nonlinearGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData) state)
  have hSum :=
    @HasFDerivAt.add Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance _ _ _ _ state hPhysical hBRST
  convert hSum using 1
  all_goals rfl

theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_contDiffAt_two
    (state : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
      period hPeriod configuration data analysis chartData)
    (hState : state ∈
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData) :
    @ContDiffAt Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance 2
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period
        hPeriod configuration data analysis chartData) state := by
  change
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData state ∈
      (MinimalChart period hPeriod configuration data analysis chartData).family.domain
    at hState
  have hPhysicalProjection :
      @ContDiffAt Real alignedRealNontriviallyNormedField
        (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
          period hPeriod configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (MinimalChart period hPeriod configuration data analysis chartData).Model
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedSpace
        2
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData) state :=
    @ContDiff.contDiffAt Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedAddCommGroup
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedSpace
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData)
      state 2
      (@ContinuousLinearMap.contDiff Real
        (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
          period hPeriod configuration data analysis chartData)
        (MinimalChart period hPeriod configuration data analysis chartData).Model
        alignedRealNontriviallyNormedField
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedAddCommGroup
        (MinimalChart period hPeriod configuration data analysis
          chartData).normedSpace
        2
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData))
  have hGraphProjection :
      @ContDiffAt Real alignedRealNontriviallyNormedField
        (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
          period hPeriod configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (DiffeomorphismGraph period hPeriod configuration data)
        (nonlinearGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (nonlinearGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        2
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData) state :=
    @ContDiff.contDiffAt Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (DiffeomorphismGraph period hPeriod configuration data)
      (nonlinearGraphNormedAddCommGroup period hPeriod
        (BaseMetric period hPeriod configuration data))
      (nonlinearGraphNormedSpace period hPeriod
        (BaseMetric period hPeriod configuration data))
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData)
      state 2
      (@ContinuousLinearMap.contDiff Real
        (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
          period hPeriod configuration data analysis chartData)
        (DiffeomorphismGraph period hPeriod configuration data)
        alignedRealNontriviallyNormedField
        (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
          configuration data analysis chartData)
        (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
          configuration data analysis chartData)
        (nonlinearGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (nonlinearGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        2
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData))
  have hPhysical :=
    @ContDiffAt.comp Real
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis chartData).Model
      Real alignedRealNontriviallyNormedField
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedAddCommGroup
      (MinimalChart period hPeriod configuration data analysis
        chartData).normedSpace
      inferInstance inferInstance
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateALocalActionPullback period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData))
      2
      state
      (globalCandidateALocalActionPullback_contDiffAt_two period hPeriod
        (MinimalChart period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData state) hState)
      hPhysicalProjection
  have hBRST :=
    @ContDiffAt.comp Real
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (DiffeomorphismGraph period hPeriod configuration data)
      Real alignedRealNontriviallyNormedField
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      (nonlinearGraphNormedAddCommGroup period hPeriod
        (BaseMetric period hPeriod configuration data))
      (nonlinearGraphNormedSpace period hPeriod
        (BaseMetric period hPeriod configuration data))
      inferInstance inferInstance
      (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
        period hPeriod configuration data analysis chartData)
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
        couplings (BaseMetric period hPeriod configuration data))
      2
      state
      (@ContDiff.contDiffAt Real alignedRealNontriviallyNormedField
        (DiffeomorphismGraph period hPeriod configuration data)
        (nonlinearGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (nonlinearGraphNormedSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        Real inferInstance inferInstance
        (globalCandidateADiagonalDiffeomorphismOffShellGraphAction period hPeriod
          couplings (BaseMetric period hPeriod configuration data))
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData state)
        2
        (globalCandidateADiagonalDiffeomorphismOffShellGraphAction_contDiff_two
          period hPeriod couplings
          (BaseMetric period hPeriod configuration data)))
      hGraphProjection
  have hSum :=
    @ContDiffAt.add Real alignedRealNontriviallyNormedField
      (GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedAddCommGroup period hPeriod
        configuration data analysis chartData)
      (nonlinearBRSTGraphChartNormedSpace period hPeriod (measure := measure)
        configuration data analysis chartData)
      Real inferInstance inferInstance state 2 _ _ hPhysical hBRST
  convert hSum using 1
  all_goals rfl

/-- The completed BRST factor keeps its strong Riesz representative after
restriction to the shared-metric relational chart. -/
theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTRieszContribution_pairing
    (state test : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
      period hPeriod configuration data analysis chartData) :
    inner Real
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period hPeriod
          couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
            period hPeriod configuration data analysis chartData state))
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData test) =
      globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData test) :=
  globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing
    period hPeriod couplings (BaseMetric period hPeriod configuration data) _ _

private theorem zeroGlobalDiffeomorphismAntighostField_field
    : (zeroGlobalDiffeomorphismAntighostField period hPeriod).field = 0 := by
  apply ContMDiffSection.ext
  intro point
  rfl

private theorem zeroGlobalDiffeomorphismNakanishiLautrupField_field
    : (zeroGlobalDiffeomorphismNakanishiLautrupField period hPeriod).field = 0 := by
  apply ContMDiffSection.ext
  intro point
  rfl

private theorem globalIntegratedCovectorVectorPairing_zero_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (covector :
      EffectiveD8SmoothCovectorField
        (generalMetricDivergenceBackground period hPeriod)) :
    globalIntegratedCovectorVectorPairing period hPeriod metric covector 0 = 0 := by
  rw [← globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing,
    (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).map_zero,
    inner_zero_right]

/-- Turning off the shared `c/cbar/B` triplet removes the entire
diffeomorphism gauge-fixing contribution, without constraining the metric
perturbation. -/
theorem globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_zero_nonminimal
    (metricPerturbation : GlobalMetricPerturbationPair period hPeriod) :
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod couplings (BaseMetric period hPeriod configuration data)
        { metricPerturbation := metricPerturbation
          nonminimal := zeroGlobalDiffeomorphismNonminimalFields period hPeriod } = 0 := by
  rw [globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_formula]
  unfold globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
    globalDiffeomorphismGaugeFermionBRSTMixedAction
  simp only [globalCandidateADiagonalDiffeomorphismSectorState_nonminimal,
    zeroGlobalDiffeomorphismNonminimalFields,
    zeroGlobalDiffeomorphismAntighostField_field,
    zeroGlobalDiffeomorphismNakanishiLautrupField_field,
    globalIntegratedCovectorVectorPairing_zero_right, mul_zero, sub_zero,
    add_zero]

/-- On the canonical core the action is exactly the nonlinear covariant action
plus the genuine diffeomorphism gauge-fermion BRST variation. -/
theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_core_eq
    (core : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D
      period hPeriod configuration)
    (hCore :
      (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData) core.1 ∈
        (MinimalChart period hPeriod configuration data analysis chartData).family.domain) :
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData core) =
      globalCandidateACovariantAction period hPeriod
          ((MinimalChart period hPeriod configuration data analysis chartData).family.datumAt
            ((globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
              configuration data analysis chartData) core.1) hCore).2 measure +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
          period hPeriod couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
            period hPeriod configuration core) := by
  unfold globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection_core,
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection_core,
    globalCandidateALocalActionPullback_eq_covariant_of_mem period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      _ hCore,
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction_smooth_eq_BRST]

/-- On the zero-nonminimal slice the nonlinear augmented action is exactly
the covariant physical action. -/
theorem globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_zero_nonminimal_eq
    (physical : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPhysical :
      (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData) physical ∈
        (MinimalChart period hPeriod configuration data analysis chartData).family.domain) :
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData
          (physical, zeroGlobalDiffeomorphismNonminimalFields period hPeriod)) =
      globalCandidateACovariantAction period hPeriod
        ((MinimalChart period hPeriod configuration data analysis chartData).family.datumAt
          ((globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
            configuration data analysis chartData) physical) hPhysical).2 measure := by
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_core_eq
    period hPeriod configuration data analysis chartData
    (physical, zeroGlobalDiffeomorphismNonminimalFields period hPeriod) hPhysical]
  change _ +
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod couplings (BaseMetric period hPeriod configuration data)
        { metricPerturbation := physical.1.completeVariation.fullMetricPerturbation
          nonminimal := zeroGlobalDiffeomorphismNonminimalFields period hPeriod } = _
  rw [globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_zero_nonminimal,
    add_zero]

/-- Gate 222: the exact nonlinear physical chart and the completed diagonal
diffeomorphism graph form one faithful shared-metric relational chart. -/
theorem global_candidateA_gaugeFixed_nonlinear_diffeomorphism_BRST_graph_chart_gate :
    IsOpen
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
          configuration data analysis chartData) ∧
      (0 : GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
        period hPeriod configuration data analysis chartData) ∈
          globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
            configuration data analysis chartData ∧
      Function.Bijective
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData) := by
  exact ⟨globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain_isOpen
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain_zero_mem
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_injective
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_surjective
      period hPeriod configuration data analysis chartData⟩

end SharedMetricChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
end JanusFormal
