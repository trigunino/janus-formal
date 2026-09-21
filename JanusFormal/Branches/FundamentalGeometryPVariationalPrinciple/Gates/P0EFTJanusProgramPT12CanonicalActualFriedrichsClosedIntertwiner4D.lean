import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D

/-!
The smooth-core intertwining packet extends by density and closedness to the
whole actual Hilbert space along its ambient isometric image.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12CanonicalActualFriedrichsClosedIntertwiner4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D
open P0EFTJanusProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

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

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period
  hPeriod (measure := measure) configuration data analysis)
variable (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
  period hPeriod configuration data analysis chartData)

private abbrev CanonicalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev CanonicalSameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev CanonicalPhysical :=
  globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
    configuration data analysis chartData reducedChart

private abbrev SmoothCore :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev ActualHilbert :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

private abbrev FriedrichsHilbert (iota : Type*) :=
  ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
    analysis

private def smoothEmbedding :
    SmoothCore period hPeriod configuration analysis →ₗ[Real]
      ActualHilbert period hPeriod configuration data analysis :=
  diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

private abbrev ActualOperator :=
  globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
    configuration data analysis chartData reducedChart

private abbrev PhysicalZeroOperator
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    FriedrichsHilbert period hPeriod configuration analysis iota →ₗ.[Real]
      FriedrichsHilbert period hPeriod configuration analysis iota :=
  programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
    (configuration := configuration) (data := data) (analysis := analysis)
      (chart := CanonicalChart period hPeriod configuration data analysis
        chartData)
      (sameAction := CanonicalSameAction period hPeriod configuration data
        analysis chartData)
      (physical := CanonicalPhysical period hPeriod configuration data analysis
        chartData reducedChart)
      period hPeriod covector 0

/-- Closedness extends the smooth-core graph intertwining to every state in
the actual Hilbert completion. -/
theorem ambient_graph_mem
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (bridge : ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
      period hPeriod configuration data analysis chartData reducedChart
        covector)
    (state : ActualHilbert period hPeriod configuration data analysis) :
    (bridge.ambient state,
        bridge.ambient
          (ActualOperator period hPeriod configuration data analysis chartData
            reducedChart state)) ∈
      (PhysicalZeroOperator period hPeriod configuration data analysis chartData
        reducedChart covector).graph := by
  let graphMap : ActualHilbert period hPeriod configuration data analysis →
      FriedrichsHilbert period hPeriod configuration analysis iota ×
        FriedrichsHilbert period hPeriod configuration analysis iota :=
    fun value ↦
      (bridge.ambient value,
        bridge.ambient
          (ActualOperator period hPeriod configuration data analysis chartData
            reducedChart value))
  let good : Set (ActualHilbert period hPeriod configuration data analysis) :=
    graphMap ⁻¹'
      ((PhysicalZeroOperator period hPeriod configuration data analysis chartData
        reducedChart covector).graph : Set _)
  have hGraphMapContinuous : Continuous graphMap :=
    bridge.ambient.continuous.prodMk
      (bridge.ambient.continuous.comp
        (ActualOperator period hPeriod configuration data analysis chartData
          reducedChart).continuous)
  have hGoodClosed : IsClosed good :=
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_closed
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := CanonicalChart period hPeriod configuration data analysis
          chartData)
        (sameAction := CanonicalSameAction period hPeriod configuration data
          analysis chartData)
        (physical := CanonicalPhysical period hPeriod configuration data analysis
          chartData reducedChart)
        period hPeriod covector 0).preimage hGraphMapContinuous
  have hCore : Set.range
      (smoothEmbedding period hPeriod configuration data analysis) ⊆ good := by
    rintro _ ⟨core, rfl⟩
    change
      (bridge.ambient
          (smoothEmbedding period hPeriod configuration data analysis core),
        bridge.ambient
          (ActualOperator period hPeriod configuration data analysis chartData
            reducedChart
            (smoothEmbedding period hPeriod configuration data analysis core))) ∈
        (PhysicalZeroOperator period hPeriod configuration data analysis chartData
          reducedChart covector).graph
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨bridge.ambient
        (smoothEmbedding period hPeriod configuration data analysis core),
      bridge.smooth_mem_domain core⟩, rfl, ?_⟩
    exact bridge.intertwines core
  have hDense : DenseRange
      (smoothEmbedding period hPeriod configuration data analysis) :=
    diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  have hState : state ∈ closure (Set.range
      (smoothEmbedding period hPeriod configuration data analysis)) := by
    rw [hDense.closure_range]
    trivial
  exact (closure_minimal hCore hGoodClosed) hState

/-- Every actual Hilbert state maps into the zero-fibre domain. -/
theorem ambient_mem_domain
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (bridge : ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
      period hPeriod configuration data analysis chartData reducedChart
        covector)
    (state : ActualHilbert period hPeriod configuration data analysis) :
    bridge.ambient state ∈
      (PhysicalZeroOperator period hPeriod configuration data analysis chartData
        reducedChart covector).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (ambient_graph_mem period hPeriod configuration data analysis chartData
      reducedChart covector bridge state)

/-- The zero fibre intertwines the actual bounded Hessian on the whole actual
Hilbert completion. -/
theorem intertwines_all
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (bridge : ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
      period hPeriod configuration data analysis chartData reducedChart
        covector)
    (state : ActualHilbert period hPeriod configuration data analysis) :
    PhysicalZeroOperator period hPeriod configuration data analysis chartData
        reducedChart covector
        ⟨bridge.ambient state,
          ambient_mem_domain period hPeriod configuration data analysis chartData
            reducedChart covector bridge state⟩ =
      bridge.ambient
        (ActualOperator period hPeriod configuration data analysis chartData
          reducedChart state) := by
  have hGraph :=
    ambient_graph_mem period hPeriod configuration data analysis chartData
      reducedChart covector bridge state
  rw [LinearPMap.mem_graph_iff] at hGraph
  rcases hGraph with ⟨domainState, hValue, hOperator⟩
  have hDomainState : domainState =
      ⟨bridge.ambient state,
        ambient_mem_domain period hPeriod configuration data analysis chartData
          reducedChart covector bridge state⟩ := by
    apply Subtype.ext
    simpa using hValue
  rw [← hDomainState]
  simpa using hOperator

end
end
end P0EFTJanusProgramPT12CanonicalActualFriedrichsClosedIntertwiner4D
end JanusFormal
