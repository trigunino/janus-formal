import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingThreeRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D

/-!
# Common fixed carrier for the three full-BRST LL coordinates

All three LL base maps land in the same state-independent complete graph
Hilbert space. Their pure-slot ranges are different, so each coordinate uses
its own closed carrier inside that common ambient space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

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

section LLFixedCarrier

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

/-- The genuine state-independent base shared by all three LL coordinates. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient :=
  GlobalFullLLGraphHilbert period hPeriod data analysis

@[implicit_reducible]
local instance (priority := 12000)
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
  globalFullLLGraphInnerProductSpace period hPeriod data analysis

local instance (priority := 12000)
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
  globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis

/-- Dense combined smooth core of the common LL ambient space. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding
        period hPeriod configuration data analysis) :=
  globalCandidateAFullLLSmoothEmbedding_denseRange period hPeriod data analysis

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding
        period hPeriod configuration data analysis) :=
  globalCandidateAFullLLSmoothEmbedding_injective period hPeriod data analysis

/-- Auxiliary-metric pure-slot map into the common LL ambient space. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period hPeriod
    configuration data analysis chartData

/-- Measure pure-slot map into the common LL ambient space. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period hPeriod
    configuration data analysis chartData

/-- Field pure-slot map into the common LL ambient space. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
    configuration data analysis chartData

/-- Closed fixed carrier of the LL auxiliary-metric pure slot. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedClosure :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap period
      hPeriod configuration data analysis chartData)).topologicalClosure

/-- Closed fixed carrier of the LL measure pure slot. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedClosure :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap period
      hPeriod configuration data analysis chartData)).topologicalClosure

/-- Closed fixed carrier of the LL field pure slot. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedClosure :
    Submodule Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
  (LinearMap.range
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap period
      hPeriod configuration data analysis chartData)).topologicalClosure

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedClosure period
    hPeriod configuration data analysis chartData

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedClosure period
    hPeriod configuration data analysis chartData

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedClosure period hPeriod
    configuration data analysis chartData

/-! The carrier structures are named explicitly so downstream LL regularity
gates can reactivate one coherent hierarchy instead of relying on competing
subtype inference paths. -/

@[implicit_reducible]
local instance (priority := 10001) llAuxMetricFixedNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
      hPeriod configuration data analysis)
    inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
    inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedClosure period
      hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) llAuxMetricFixedPseudoMetricSpace :
    PseudoMetricSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) llAuxMetricFixedUniformSpace :
    UniformSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedPseudoMetricSpace period hPeriod configuration data analysis
    chartData).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) llAuxMetricFixedSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) llAuxMetricFixedAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) llAuxMetricFixedTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedUniformSpace period hPeriod configuration data analysis
    chartData).toTopologicalSpace

local instance (priority := 10001) llAuxMetricFixedInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
      hPeriod configuration data analysis)
    inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup.toSeminormedAddCommGroup
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedClosure period
      hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10001) llAuxMetricFixedNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedInnerProductSpace period hPeriod configuration data analysis
    chartData).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) llAuxMetricFixedModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llAuxMetricFixedNormedSpace period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) llMeasureFixedNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
      hPeriod configuration data analysis)
    inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
    inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedClosure period
      hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) llMeasureFixedPseudoMetricSpace :
    PseudoMetricSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) llMeasureFixedUniformSpace :
    UniformSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedPseudoMetricSpace period hPeriod configuration data analysis
    chartData).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) llMeasureFixedSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) llMeasureFixedAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) llMeasureFixedTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedUniformSpace period hPeriod configuration data analysis
    chartData).toTopologicalSpace

local instance (priority := 10001) llMeasureFixedInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
      hPeriod configuration data analysis)
    inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup.toSeminormedAddCommGroup
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedClosure period
      hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10001) llMeasureFixedNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedInnerProductSpace period hPeriod configuration data analysis
    chartData).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) llMeasureFixedModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llMeasureFixedNormedSpace period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) llFieldFixedNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
      hPeriod configuration data analysis)
    inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
    inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedClosure period
      hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) llFieldFixedPseudoMetricSpace :
    PseudoMetricSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 10003) llFieldFixedUniformSpace :
    UniformSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedPseudoMetricSpace period hPeriod configuration data analysis
    chartData).toUniformSpace

@[implicit_reducible]
local instance (priority := 10002) llFieldFixedSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) llFieldFixedAddCommGroup :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) llFieldFixedTopologicalSpace :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedUniformSpace period hPeriod configuration data analysis
    chartData).toTopologicalSpace

local instance (priority := 10001) llFieldFixedInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  @Submodule.innerProductSpace Real
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
      hPeriod configuration data analysis)
    inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup.toSeminormedAddCommGroup
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
      period hPeriod configuration data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedClosure period
      hPeriod configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10001) llFieldFixedNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedInnerProductSpace period hPeriod configuration data analysis
    chartData).toNormedSpace

@[implicit_reducible]
local instance (priority := 10001) llFieldFixedModule :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) :=
  (llFieldFixedNormedSpace period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData) := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
      period hPeriod configuration data analysis
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap period
        hPeriod configuration data analysis chartData))

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData) := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
      period hPeriod configuration data analysis
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap period
        hPeriod configuration data analysis chartData))

@[implicit_reducible]
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedCompleteSpace :
    CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData) := by
  letI : CompleteSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis) :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
      period hPeriod configuration data analysis
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap period
        hPeriod configuration data analysis chartData))

/-- Canonical inclusion of the auxiliary-metric carrier into the common base. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedInclusionCLM :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  Submodule.subtypeL
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedClosure period
      hPeriod configuration data analysis chartData)

/-- Canonical inclusion of the measure carrier into the common base. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedInclusionCLM :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  Submodule.subtypeL
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedClosure period
      hPeriod configuration data analysis chartData)

/-- Canonical inclusion of the field carrier into the common base. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedInclusionCLM :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData →L[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis :=
  Submodule.subtypeL
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedClosure period
      hPeriod configuration data analysis chartData)

/-- Dense pure auxiliary-metric core in its fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
        hPeriod configuration data analysis chartData where
  toFun test :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap period
        hPeriod configuration data analysis chartData test,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap
          period hPeriod configuration data analysis chartData)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap
            period hPeriod configuration data analysis chartData) test)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar test := Subtype.ext (map_smul _ scalar test)

/-- Dense pure measure core in its fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
        hPeriod configuration data analysis chartData where
  toFun test :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap period
        hPeriod configuration data analysis chartData test,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap
          period hPeriod configuration data analysis chartData)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap
            period hPeriod configuration data analysis chartData) test)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar test := Subtype.ext (map_smul _ scalar test)

/-- Dense pure field core in its fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
        hPeriod configuration data analysis chartData where
  toFun test :=
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap period
        hPeriod configuration data analysis chartData test,
      (LinearMap.range
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap period
          hPeriod configuration data analysis chartData)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap period
            hPeriod configuration data analysis chartData) test)⟩
  map_add' first second := Subtype.ext (map_add _ first second)
  map_smul' scalar test := Subtype.ext (map_smul _ scalar test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseMap period
      hPeriod configuration data analysis chartData
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient
            period hPeriod configuration data analysis)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test,
          ⟨test, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
        period hPeriod configuration data analysis chartData))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseMap period
      hPeriod configuration data analysis chartData
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient
            period hPeriod configuration data analysis)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test,
          ⟨test, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
        period hPeriod configuration data analysis chartData))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding_denseRange :
    DenseRange
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let coordinate :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseMap period
      hPeriod configuration data analysis chartData
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) =
        (LinearMap.range coordinate : Set
          (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient
            period hPeriod configuration data analysis)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨test, rfl⟩, rfl⟩
      exact ⟨test, rfl⟩
    · rintro ⟨test, rfl⟩
      exact
        ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test,
          ⟨test, rfl⟩, rfl⟩
  change closure (LinearMap.range coordinate : Set
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
        hPeriod configuration data analysis)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
        period hPeriod configuration data analysis chartData))
  rw [hRange]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_injective
      period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_injective
    period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_injective
    period hPeriod configuration data analysis chartData
  exact congrArg Subtype.val hEqual

/-- Gate 309: the three LL coordinates share one fixed complete ambient base
and have their own fixed complete carriers with dense injective pure cores. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_common_fixed_carrier_gate :
    DenseRange
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding
          period hPeriod configuration data analysis) ∧
      Function.Injective
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding
          period hPeriod configuration data analysis) ∧
      (DenseRange
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) ∧
        Function.Injective
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding
            period hPeriod configuration data analysis chartData)) ∧
      (DenseRange
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) ∧
        Function.Injective
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding
            period hPeriod configuration data analysis chartData)) ∧
      (DenseRange
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
            period hPeriod configuration data analysis chartData) ∧
        Function.Injective
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding
            period hPeriod configuration data analysis chartData)) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding_denseRange
      period hPeriod configuration data analysis,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedSmoothEmbedding_injective
      period hPeriod configuration data analysis,
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding_denseRange
        period hPeriod configuration data analysis chartData,
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedDenseEmbedding_injective
        period hPeriod configuration data analysis chartData⟩,
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding_denseRange
        period hPeriod configuration data analysis chartData,
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedDenseEmbedding_injective
        period hPeriod configuration data analysis chartData⟩,
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding_denseRange
        period hPeriod configuration data analysis chartData,
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedDenseEmbedding_injective
        period hPeriod configuration data analysis chartData⟩⟩

end LLFixedCarrier
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D
end JanusFormal
