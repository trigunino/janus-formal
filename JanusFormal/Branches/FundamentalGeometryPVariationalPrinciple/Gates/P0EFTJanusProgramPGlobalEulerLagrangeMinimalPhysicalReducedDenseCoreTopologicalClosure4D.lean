import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreClosureOfHilbertChart4D

/-!
# Topological dense-core closure of the reduced physical chart

Exact equality of the chart and reduced-Hilbert norms is stronger than needed.
Two uniform comparison bounds on the dense quotient core extend its algebraic
identification to a continuous linear equivalence of the completions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreTopologicalClosure4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreClosureOfHilbertChart4D

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

local instance reducedTopologicalCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedTopologicalCommonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedTopologicalCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedTopologicalCommonInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance reducedTopologicalCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedTopologicalCommonNormedSpace period hPeriod configuration data
    analysis).toModule

local instance reducedTopologicalCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Honest topological closure data.  The two norms need only be uniformly
equivalent on the quotient smooth core, not exactly equal. -/
structure ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D where
  chartComplete : CompleteSpace
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model
  forward_bound : ∃ constant : Real,
    ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis,
      ‖globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData core‖ ≤
        constant *
          ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis core‖
  inverse_bound : ∃ constant : Real,
    ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis,
      ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis core‖ ≤
        constant *
          ‖globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData core‖
  dense_range : DenseRange
    (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
      configuration data analysis chartData)

/-- The earlier isometric closure packet is a special case of topological
closure with both comparison constants equal to one. -/
def ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D.ofIsometric
    (closure : ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D
      period hPeriod configuration data analysis chartData) :
    ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D
      period hPeriod configuration data analysis chartData where
  chartComplete := closure.chartComplete
  forward_bound := ⟨1, by
    intro core
    rw [closure.norm_compatibility core]
    simp only [one_mul, le_refl]⟩
  inverse_bound := ⟨1, by
    intro core
    rw [closure.norm_compatibility core]
    simp only [one_mul, le_refl]⟩
  dense_range := closure.dense_range

/-- Uniformly equivalent dense-core norms construct the reduced Hilbert chart
without choosing an artificial isometric normalization. -/
def globalCandidateAMinimalPhysicalReducedHilbertChartOfTopologicalDenseCoreClosure
    (closure :
      ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D
        period hPeriod configuration data analysis chartData) :
    ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period hPeriod
      configuration data analysis chartData := by
  letI chartModelCompleteSpace : CompleteSpace
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
    closure.chartComplete
  let coreToChart := globalCandidateAMinimalPhysicalReducedCoreToChart period
    hPeriod configuration data analysis chartData
  let reducedEmbedding :=
    globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
      hPeriod configuration data analysis
  have hInjective : Function.Injective coreToChart :=
    globalCandidateAMinimalPhysicalReducedCoreToChart_injective period hPeriod
      configuration data analysis chartData
  let coreEquiv :
      GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
          configuration data analysis ≃ₗ[Real]
        LinearMap.range coreToChart :=
    LinearEquiv.ofInjective coreToChart hInjective
  let rangeInclusion : LinearMap.range coreToChart →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
    Submodule.subtype (LinearMap.range coreToChart)
  have hSmoothDense : DenseRange reducedEmbedding :=
    globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_denseRange
      period hPeriod configuration data analysis
  have hRangeDense : DenseRange rangeInclusion := by
    apply DenseRange.of_comp (f := rangeInclusion) (g := coreEquiv)
    simpa [Function.comp_def, rangeInclusion, coreEquiv, coreToChart] using
      closure.dense_range
  have hForward : ∃ constant : Real, ∀ core,
      ‖rangeInclusion (coreEquiv core)‖ ≤
        constant * ‖reducedEmbedding core‖ := by
    rcases closure.forward_bound with ⟨constant, hBound⟩
    refine ⟨constant, ?_⟩
    intro core
    simpa [rangeInclusion, coreEquiv, coreToChart, reducedEmbedding] using
      hBound core
  have hInverse : ∃ constant : Real, ∀ value,
      ‖reducedEmbedding (coreEquiv.symm value)‖ ≤
        constant * ‖rangeInclusion value‖ := by
    rcases closure.inverse_bound with ⟨constant, hBound⟩
    refine ⟨constant, ?_⟩
    intro value
    simpa [rangeInclusion, coreEquiv, coreToChart, reducedEmbedding] using
      hBound (coreEquiv.symm value)
  let extended :
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
          configuration data analysis ≃L[Real]
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).Model :=
    coreEquiv.extend reducedEmbedding rangeInclusion hSmoothDense hForward
      hRangeDense hInverse
  have hExtendedCore : ∀ core,
      extended (reducedEmbedding core) = coreToChart core := by
    intro core
    exact LinearEquiv.extend_eq coreEquiv reducedEmbedding rangeInclusion
      hSmoothDense hForward hRangeDense hInverse core
  refine
    { toChart := extended
      quotient_core_compatibility := ?_ }
  intro core
  exact hExtendedCore core

/-- Every already constructed reduced Hilbert chart satisfies the topological
closure criterion, with constants given by the two operator norms. -/
def globalCandidateAMinimalPhysicalReducedDenseCoreTopologicalClosure_of_hilbertChart
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData) :
    ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D
      period hPeriod configuration data analysis chartData where
  chartComplete :=
    globalCandidateAMinimalPhysicalReducedChartComplete_of_hilbertChart period
      hPeriod configuration data analysis chartData reducedChart
  forward_bound :=
    ⟨‖reducedChart.toChart.toContinuousLinearMap‖, by
      intro core
      rw [← reducedChart.quotient_core_compatibility core]
      exact reducedChart.toChart.toContinuousLinearMap.le_opNorm _⟩
  inverse_bound :=
    ⟨‖reducedChart.toChart.symm.toContinuousLinearMap‖, by
      intro core
      rw [← reducedChart.quotient_core_compatibility core]
      simpa using
        reducedChart.toChart.symm.toContinuousLinearMap.le_opNorm
          (reducedChart.toChart
            (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
              period hPeriod configuration data analysis core))⟩
  dense_range :=
    globalCandidateAMinimalPhysicalReducedCoreToChart_denseRange_of_hilbertChart
      period hPeriod configuration data analysis chartData reducedChart

/-- The two-bound dense-core criterion is exactly equivalent to existence of
a reduced continuous linear Hilbert chart. -/
theorem globalCandidateAMinimalPhysicalReducedDenseCoreTopologicalClosure_nonempty_iff_hilbertChart_nonempty :
    Nonempty
        (ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D
          period hPeriod configuration data analysis chartData) ↔
      Nonempty
        (ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period hPeriod
          configuration data analysis chartData) := by
  constructor
  · rintro ⟨closure⟩
    exact
      ⟨globalCandidateAMinimalPhysicalReducedHilbertChartOfTopologicalDenseCoreClosure
        period hPeriod configuration data analysis chartData closure⟩
  · rintro ⟨reducedChart⟩
    exact
      ⟨globalCandidateAMinimalPhysicalReducedDenseCoreTopologicalClosure_of_hilbertChart
        period hPeriod configuration data analysis chartData reducedChart⟩

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreTopologicalClosure4D
end JanusFormal
