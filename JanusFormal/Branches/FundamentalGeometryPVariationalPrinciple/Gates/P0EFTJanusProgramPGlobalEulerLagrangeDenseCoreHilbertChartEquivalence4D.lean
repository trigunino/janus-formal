import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreChartRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

/-!
# Hilbert chart equivalence from an isometric dense smooth core

The previously supplied continuous Hilbert-chart equivalence is constructed
canonically once the chart model is complete, the genuine core-to-chart map
preserves the common graph norm, and its range is dense.  Mathlib's isometric
dense extension supplies both the bounded map and its inverse.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

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

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)

local instance denseCoreCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance denseCoreCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance denseCoreCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance denseCoreCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The genuine smooth-core embedding, with its target instances fixed to the
common Hilbert chart contract. -/
def globalCandidateACommonHilbertSmoothCoreEmbedding :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
        CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
        CommonAugmentedHilbert period hPeriod configuration data analysis)

/-- Equality of the core norm with the common graph norm makes the genuine
core-to-chart map injective. -/
theorem globalCandidateACanonicalSixCoreToChart_injective_of_norm
    (hNorm : ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period
        hPeriod analysis,
      ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
          analysis chart sameAction core‖ =
        ‖globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core‖) :
    Function.Injective
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction) := by
  intro first second hEqual
  have hNormZero :
      ‖globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis (first - second)‖ = 0 := by
    rw [← hNorm (first - second), map_sub, hEqual, sub_self, norm_zero]
  have hEmbeddingZero :
      globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis (first - second) = 0 :=
    norm_eq_zero.mp hNormZero
  have hRawEmbeddingZero :
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis (first - second) =
        diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis 0 := by
    change
      globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis (first - second) =
        globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis 0
    simpa only [map_zero] using hEmbeddingZero
  have hSubZero : first - second = 0 :=
    diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis hRawEmbeddingZero
  exact sub_eq_zero.mp hSubZero

variable [CompleteSpace chart.Model]

/-- Canonical common-Hilbert chart equivalence obtained by extending the
isometric dense smooth-core identification. -/
def globalCandidateACommonHilbertChartOfDenseCoreIsometry
    (hNorm : ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period
        hPeriod analysis,
      ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
          analysis chart sameAction core‖ =
        ‖globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core‖)
    (hDense : DenseRange
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction)) :
    ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period hPeriod
      configuration data analysis chart sameAction := by
  let coreToChart := globalCandidateACanonicalSixCoreToChart period hPeriod
    configuration data analysis chart sameAction
  let smoothEmbedding := globalCandidateACommonHilbertSmoothCoreEmbedding
    period hPeriod configuration data analysis
  have hInjective : Function.Injective coreToChart :=
    globalCandidateACanonicalSixCoreToChart_injective_of_norm period hPeriod
      configuration data analysis chart sameAction hNorm
  let coreEquiv :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
        ≃ₗ[Real] LinearMap.range coreToChart :=
    LinearEquiv.ofInjective coreToChart hInjective
  let rangeInclusion : LinearMap.range coreToChart →ₗ[Real] chart.Model :=
    Submodule.subtype (LinearMap.range coreToChart)
  have hSmoothDense : DenseRange smoothEmbedding :=
    diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  have hRangeDense : DenseRange rangeInclusion := by
    apply DenseRange.of_comp (f := rangeInclusion) (g := coreEquiv)
    simpa [Function.comp_def, rangeInclusion, coreEquiv, coreToChart] using hDense
  have hIsometry : ∀ core, ‖rangeInclusion (coreEquiv core)‖ =
      ‖smoothEmbedding core‖ := by
    intro core
    simpa [rangeInclusion, coreEquiv, coreToChart, smoothEmbedding] using
      hNorm core
  let extended :
      CommonAugmentedHilbert period hPeriod configuration data analysis
        ≃ₗᵢ[Real] chart.Model :=
    coreEquiv.extendOfIsometry smoothEmbedding rangeInclusion hSmoothDense
      hRangeDense hIsometry
  have hExtendedCore : ∀ core,
      extended (smoothEmbedding core) = coreToChart core := by
    intro core
    exact LinearEquiv.extendOfIsometry_eq coreEquiv smoothEmbedding
      rangeInclusion hSmoothDense hRangeDense hIsometry core
  refine
    { toChart := extended.toContinuousLinearEquiv
      smooth_core_compatibility := ?_ }
  intro core
  dsimp only [extended]
  have hInput :
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core =
        smoothEmbedding core := rfl
  rw [hInput]
  exact (hExtendedCore core).trans rfl

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
end JanusFormal
