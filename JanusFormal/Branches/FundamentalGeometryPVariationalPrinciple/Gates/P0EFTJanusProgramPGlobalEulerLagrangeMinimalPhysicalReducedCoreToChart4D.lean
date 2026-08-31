import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D

/-!
# Minimal physical quotient core-to-chart map

The concrete minimal chart map has exactly the canonical physical smooth-core
kernel.  It therefore descends injectively to the quotient core used by the
reduced Hilbert completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D

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
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

/-- The concrete minimal chart forgets precisely the kernel already used to
define the reduced smooth core. -/
theorem globalCandidateAMinimalPhysicalCanonicalCoreToChart_ker :
    LinearMap.ker
        (globalCandidateACanonicalSixCoreToChart period hPeriod configuration
          data analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
            hPeriod configuration data analysis chartData)) =
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis := by
  ext core
  constructor
  · intro hCore
    have hChart := LinearMap.mem_ker.mp hCore
    change
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core) = 0 at hChart
    apply LinearMap.mem_ker.mpr
    exact
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.tangentAnalysis_injective
          (by simpa only [LinearMap.map_zero] using hChart)
  · intro hCore
    have hTangent := LinearMap.mem_ker.mp hCore
    apply LinearMap.mem_ker.mpr
    change
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core) = 0
    rw [hTangent]
    exact LinearMap.map_zero _

/-- Canonical core-to-chart map on the physical quotient core. -/
def globalCandidateAMinimalPhysicalReducedCoreToChart :
    GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
    configuration data analysis).liftQ (τ₁₂ := RingHom.id Real)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)) (by
            rw [← globalCandidateAMinimalPhysicalCanonicalCoreToChart_ker
              period hPeriod configuration data analysis chartData])

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCoreToChart_mk
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData (Submodule.Quotient.mk core) =
      globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) core :=
  rfl

/-- No further algebraic kernel remains after quotienting. -/
theorem globalCandidateAMinimalPhysicalReducedCoreToChart_injective :
    Function.Injective
      (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData) := by
  apply LinearMap.ker_eq_bot.mp
  unfold globalCandidateAMinimalPhysicalReducedCoreToChart
  apply Submodule.ker_liftQ_eq_bot
  rw [globalCandidateAMinimalPhysicalCanonicalCoreToChart_ker period hPeriod
    configuration data analysis chartData]

/-- Honest analytic obligations for identifying the reduced completion with
the concrete minimal chart. -/
structure ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D where
  chartComplete : CompleteSpace
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model
  norm_compatibility :
    ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis,
      ‖globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData core‖ =
        ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis core‖
  dense_range : DenseRange
    (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
      configuration data analysis chartData)

/-- A reduced Hilbert chart carries the canonical quotient core realization. -/
structure ProgramPGlobalMinimalPhysicalReducedHilbertChart4D where
  toChart :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis ≃L[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model
  quotient_core_compatibility :
    ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis,
      toChart
          (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis core) =
        globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData core

/-- The reduced Hilbert-chart equivalence follows canonically from the dense
quotient-core norm identity. -/
def globalCandidateAMinimalPhysicalReducedHilbertChartOfDenseCoreClosure
    (closure :
      ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D
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
  have hIsometry : ∀ core,
      ‖rangeInclusion (coreEquiv core)‖ = ‖reducedEmbedding core‖ := by
    intro core
    simpa [rangeInclusion, coreEquiv, coreToChart, reducedEmbedding] using
      closure.norm_compatibility core
  let extended :
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
          configuration data analysis ≃ₗᵢ[Real]
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).Model :=
    coreEquiv.extendOfIsometry reducedEmbedding rangeInclusion hSmoothDense
      hRangeDense hIsometry
  have hExtendedCore : ∀ core,
      extended (reducedEmbedding core) = coreToChart core := by
    intro core
    exact LinearEquiv.extendOfIsometry_eq coreEquiv reducedEmbedding
      rangeInclusion hSmoothDense hRangeDense hIsometry core
  refine
    { toChart := extended.toContinuousLinearEquiv
      quotient_core_compatibility := ?_ }
  intro core
  exact hExtendedCore core

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
end JanusFormal
