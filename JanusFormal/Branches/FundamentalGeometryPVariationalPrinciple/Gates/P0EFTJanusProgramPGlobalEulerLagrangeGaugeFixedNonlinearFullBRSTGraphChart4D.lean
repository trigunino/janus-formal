import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

/-!
# Nonlinear physical chart with the full BRST graph

This gate adds the paired Abelian off-shell graph to the exact nonlinear
physical/diffeomorphism chart.  Since the physical tangent stores frame
coefficients but has no canonical smooth inverse to intrinsic potentials, the
core is split into a gauge-free physical tangent and one intrinsic Abelian
state.  Its potential is inserted once into the physical tangent and into the
BRST graph, so the relational chart has no duplicated gauge-potential degree
of freedom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 8000000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedField :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

private theorem continuousLinearMap_comp_contDiffAt_two
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (projection : E →L[Real] F) (action : F → Real) (state : E)
    (hAction : ContDiffAt Real 2 action (projection state)) :
    ContDiffAt Real 2 (fun point => action (projection point)) state :=
  hAction.comp state projection.contDiff.contDiffAt

private theorem continuousLinearMap_add_comp_hasFDerivAt
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (first : E →L[Real] F) (second : E →L[Real] G)
    (firstAction : F → Real) (secondAction : G → Real)
    (firstDerivative : F →L[Real] Real)
    (secondDerivative : G →L[Real] Real)
    (state : E)
    (hFirst : HasFDerivAt firstAction firstDerivative (first state))
    (hSecond : HasFDerivAt secondAction secondDerivative (second state)) :
    HasFDerivAt
      (fun point => firstAction (first point) + secondAction (second point))
      (firstDerivative.comp first + secondDerivative.comp second) state :=
  (hFirst.comp state first.hasFDerivAt).add
    (hSecond.comp state second.hasFDerivAt)

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

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section FullBRSTChart

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

private abbrev DiffeomorphismChart :=
  GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D period
    hPeriod configuration data analysis chartData

private abbrev AbelianGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev FullAmbient :=
  DiffeomorphismChart period hPeriod configuration data analysis chartData ×
    AbelianGraph period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedAddCommGroup :
    NormedAddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedAddCommGroup
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedSpace :
    NormedSpace Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedSpace
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartAddCommGroup :
    AddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartTopologicalSpace :
    TopologicalSpace
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartModule :
    Module Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedSpace period hPeriod configuration data
    analysis chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedAddCommGroup :
    NormedAddCommGroup
      (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedSpace :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphAddCommGroup :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroup period hPeriod configuration
    data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphTopologicalSpace :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroup period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphModule :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedSpace period hPeriod configuration data).toModule

local instance (priority := 10002) nonlinearFullAmbientModule :
    Module Real
      (FullAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

/-- Canonical projection from a minimal physical tangent to the stored gauge
frame coefficients. -/
def globalCandidateAMinimalPhysicalGaugeCoefficientLinearMap :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →ₗ[Real] GaugeVariationPair period hPeriod where
  toFun variation :=
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      variation.1).independent.gauge
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Physical directions with no independent Abelian gauge coefficient. -/
abbrev GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D :=
  LinearMap.ker
    (globalCandidateAMinimalPhysicalGaugeCoefficientLinearMap period hPeriod
      configuration)

/-- One gauge-free physical direction, one diffeomorphism triplet and one
paired Abelian state.  The intrinsic potential occurs only in the last
factor. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D :=
  GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
      configuration ×
    (GlobalDiffeomorphismNonminimalFields period hPeriod ×
      GlobalPairedAbelianBRSTState period hPeriod)

/-- Insert the unique intrinsic Abelian potential into the gauge-free physical
tangent. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical where
  toFun core :=
    core.1.1 +
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
        hPeriod data core.2.2.potential
  map_add' first second := by
    change
      (first.1.1 + second.1.1) +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data (first.2.2.potential + second.2.2.potential) =
        (first.1.1 +
            globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
              hPeriod data first.2.2.potential) +
          (second.1.1 +
            globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
              hPeriod data second.2.2.potential)
    rw [(globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
      hPeriod data).map_add]
    abel
  map_smul' scalar core := by
    change
      scalar • core.1.1 +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data (scalar • core.2.2.potential) =
        scalar •
          (core.1.1 +
            globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
              hPeriod data core.2.2.potential)
    rw [(globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
      hPeriod data).map_smul]
    exact (smul_add scalar _ _).symm

/-- The assembled tangent has exactly the coefficients of the unique
intrinsic Abelian potential. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangent_gauge
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    globalCandidateAMinimalPhysicalGaugeCoefficientLinearMap period hPeriod
        configuration
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
          period hPeriod configuration data core) =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.2.potential := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
  change
    globalCandidateAMinimalPhysicalGaugeCoefficientLinearMap period hPeriod
        configuration
        (core.1.1 +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data core.2.2.potential) = _
  rw [(globalCandidateAMinimalPhysicalGaugeCoefficientLinearMap period hPeriod
    configuration).map_add]
  rw [LinearMap.mem_ker.mp core.1.2]
  change 0 +
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.2.potential = _
  exact zero_add _

/-- Core supplied to the already closed nonlinear diffeomorphism chart. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCore4D period
        hPeriod configuration where
  toFun core :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
      period hPeriod configuration data core, core.2.1)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
          period hPeriod configuration data).map_add first second
    · rfl
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
          period hPeriod configuration data).map_smul scalar core
    · rfl

/-- Simultaneous realization in the nonlinear diffeomorphism chart and the
paired Abelian graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      FullAmbient period hPeriod configuration data analysis chartData where
  toFun core :=
    (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
          period hPeriod configuration data core),
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (BaseMetric period hPeriod configuration data) core.2.2)
  map_add' first second := by
    apply Prod.ext
    · change
        globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
            period hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
              period hPeriod configuration data (first + second)) =
          globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
              period hPeriod configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
                period hPeriod configuration data first) +
            globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
              period hPeriod configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
                period hPeriod configuration data second)
      rw [(globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data).map_add,
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData).map_add]
    · exact
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (BaseMetric period hPeriod configuration data)).map_add
            first.2.2 second.2.2
  map_smul' scalar core := by
    apply Prod.ext
    · change
        globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
            period hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
              period hPeriod configuration data (scalar • core)) =
          scalar •
            globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
              period hPeriod configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
                period hPeriod configuration data core)
      rw [(globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data).map_smul,
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData).map_smul]
    · exact
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (BaseMetric period hPeriod configuration data)).map_smul
            scalar core.2.2

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap period
        hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  have hDiffeomorphismChart := congrArg
    (fun value : FullAmbient period hPeriod configuration data analysis
      chartData ↦ value.1) hEqual
  have hDiffeomorphismCore :=
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding_injective
      period hPeriod configuration data analysis chartData
      hDiffeomorphismChart
  have hPhysical := congrArg Prod.fst hDiffeomorphismCore
  have hDiffeomorphism := congrArg Prod.snd hDiffeomorphismCore
  have hAbelianGraph := congrArg
    (fun value : FullAmbient period hPeriod configuration data analysis
      chartData ↦ value.2) hEqual
  have hAbelian :=
    globalPairedAbelianOffShellSmoothEmbedding_injective period hPeriod
      (BaseMetric period hPeriod configuration data) hAbelianGraph
  apply Prod.ext
  · apply Subtype.ext
    change first.1.1 +
        globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
          hPeriod data first.2.2.potential =
      second.1.1 +
        globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
          hPeriod data second.2.2.potential at hPhysical
    rw [hAbelian] at hPhysical
    exact add_right_cancel hPhysical
  · apply Prod.ext
    · exact hDiffeomorphism
    · exact hAbelian

/-- Linear relation enforcing the unique-potential identification. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D :
    Submodule Real
      (FullAmbient period hPeriod configuration data analysis chartData) :=
  LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap period hPeriod
      configuration data analysis chartData)

/-- Exact nonlinear full-BRST relational chart. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D :=
  globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (FullAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (nonlinearFullAmbientModule period hPeriod (measure := measure)
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  Submodule.normedSpace
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedSpace period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Faithful realization of the algebraic full-BRST core. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
        configuration →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData where
  toFun core :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap period hPeriod
        configuration data analysis chartData core,
      LinearMap.mem_range_self
        (globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap period
          hPeriod configuration data analysis chartData) core⟩
  map_add' first second := Subtype.ext
    ((globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap period hPeriod
      configuration data analysis chartData).map_add first second)
  map_smul' scalar core := Subtype.ext
    ((globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap period hPeriod
      configuration data analysis chartData).map_smul scalar core)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis chartData) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearFullBRSTSharedLinearMap_injective
    period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_surjective :
    Function.Surjective
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis chartData) := by
  intro state
  rcases state.2 with ⟨core, hCore⟩
  exact ⟨core, Subtype.ext hCore⟩

/-- Algebraic equivalence; no completeness claim is made for this relational
range. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTCoreEquiv :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
        configuration ≃ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData :=
  LinearEquiv.ofBijective
    (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
      configuration data analysis chartData)
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_injective period
        hPeriod configuration data analysis chartData,
      globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding_surjective period
        hPeriod configuration data analysis chartData⟩

/-- Projection to the exact nonlinear physical/diffeomorphism chart. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData →L[Real]
      DiffeomorphismChart period hPeriod configuration data analysis chartData :=
  (ContinuousLinearMap.fst Real
      (DiffeomorphismChart period hPeriod configuration data analysis chartData)
      (AbelianGraph period hPeriod configuration data)).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData).subtypeL

/-- Projection to the completed paired Abelian off-shell graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData →L[Real]
      AbelianGraph period hPeriod configuration data :=
  (ContinuousLinearMap.snd Real
      (DiffeomorphismChart period hPeriod configuration data analysis chartData)
      (AbelianGraph period hPeriod configuration data)).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData).subtypeL

@[simp]
theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection_core
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData core) =
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
          period hPeriod configuration data core) :=
  rfl

@[simp]
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection_core
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData core) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (BaseMetric period hPeriod configuration data) core.2.2 :=
  rfl

/-- The only local restriction is the already established nonlinear physical
domain. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDomain :
    Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData ⁻¹'
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
      configuration data analysis chartData

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDomain_isOpen :
    IsOpen
      (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) :=
  (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain_isOpen period
      hPeriod configuration data analysis chartData).preimage
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData).continuous

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDomain_zero_mem :
    (0 : GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
      configuration data analysis chartData) ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData := by
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
        hPeriod configuration data analysis chartData 0 ∈
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain period hPeriod
        configuration data analysis chartData
  rw [map_zero]
  exact
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTDomain_zero_mem period
      hPeriod configuration data analysis chartData

end FullBRSTChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
end JanusFormal
