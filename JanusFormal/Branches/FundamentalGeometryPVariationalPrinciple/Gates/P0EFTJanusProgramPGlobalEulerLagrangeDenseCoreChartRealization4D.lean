import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAugmentedLinearizationBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixContinuousChartRieszResidual4D

/-!
# Continuous chart realization from the dense-core bound

If the local chart model is complete, the existing graph-norm estimate extends
the genuine smooth-core chart map uniquely to the common Hilbert completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreChartRealization4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertLinearization4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAugmentedLinearizationBridge4D

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
    [CompleteSpace chart.Model]
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)

local instance denseCoreCommonNormedAddCommGroup : NormedAddCommGroup
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance denseCoreCommonNormedSpace : NormedSpace Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

local instance denseCoreCommonModule : Module Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis) :=
  commonAugmentedModule period hPeriod configuration data analysis

variable (chartBound : @DenseCoreChartMapBound
      (GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis)
      (CommonAugmentedHilbert period hPeriod configuration data analysis)
      chart.Model inferInstance inferInstance
      (commonAugmentedNormedAddCommGroup period hPeriod configuration data
        analysis)
      (commonAugmentedNormedSpace period hPeriod configuration data analysis)
      chart.normedAddCommGroup chart.normedSpace
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis :
        GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
          →ₗ[Real] CommonAugmentedHilbert period hPeriod configuration data
            analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction))

private theorem smoothEmbedding_denseRange : DenseRange
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
        →ₗ[Real] CommonAugmentedHilbert period hPeriod configuration data
          analysis) :=
  diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

include chartBound

/-- Canonical continuous extension of the genuine smooth-core chart map. -/
def globalCandidateAChartRealizationOfDenseCoreBound :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      chart.Model :=
  (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
    analysis chart sameAction).extendOfNorm
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis :
        GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
          →ₗ[Real] CommonAugmentedHilbert period hPeriod configuration data
            analysis)

/-- The extension agrees exactly with the original chart map on the smooth
core. -/
theorem globalCandidateAChartRealizationOfDenseCoreBound_smooth
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAChartRealizationOfDenseCoreBound period hPeriod
        configuration data analysis chart sameAction
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core) =
      globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction core := by
  apply LinearMap.extendOfNorm_eq
  · exact smoothEmbedding_denseRange period hPeriod configuration data analysis
  · exact ⟨chartBound.constant, chartBound.estimate⟩

/-- Its operator norm is controlled by the original dense-core constant. -/
theorem globalCandidateAChartRealizationOfDenseCoreBound_opNorm_le :
    ‖globalCandidateAChartRealizationOfDenseCoreBound period hPeriod
      configuration data analysis chart sameAction‖ ≤
        chartBound.constant := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact smoothEmbedding_denseRange period hPeriod configuration data analysis
  · exact chartBound.constant_nonneg
  · exact chartBound.estimate

/-- The continuous realization is uniquely determined by its values on the
dense smooth core. -/
theorem globalCandidateAChartRealizationOfDenseCoreBound_unique
    (candidate :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (candidateAgreement : ∀ core :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis,
      candidate
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) =
        globalCandidateACanonicalSixCoreToChart period hPeriod configuration
          data analysis chart sameAction core) :
    globalCandidateAChartRealizationOfDenseCoreBound period hPeriod
      configuration data analysis chart sameAction = candidate := by
  let realization := globalCandidateAChartRealizationOfDenseCoreBound period
    hPeriod configuration data analysis chart sameAction
  have hPointwise : (fun state ↦ realization state) = fun state ↦ candidate state :=
    (smoothEmbedding_denseRange period hPeriod configuration data analysis).equalizer
      realization.continuous candidate.continuous (by
        funext core
        exact
          (globalCandidateAChartRealizationOfDenseCoreBound_smooth period hPeriod
            configuration data analysis chart sameAction chartBound core).trans
            (candidateAgreement core).symm)
  apply ContinuousLinearMap.ext
  intro state
  exact congrFun hPointwise state

/-- Hence the nonlinear residual atlas has a concrete singleton inhabitant on
the admissible preimage of the selected complete chart. -/
def globalCandidateANonlinearHilbertResidualAtlasOfDenseCoreBound :
    GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis :=
  GlobalCandidateANonlinearHilbertResidualAtlas.singleton period hPeriod chart
    sameAction.chartBridge.basePoint
    (globalCandidateAChartRealizationOfDenseCoreBound period hPeriod
      configuration data analysis chart sameAction)

/-- The resulting nonlinear linearization is the genuine covariant Hessian on
the smooth core, with no separately supplied realization agreement. -/
theorem globalCandidateANonlinearHilbertHessian_denseCoreBound_smooth_eq_covariant
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart sameAction.chartBridge.basePoint
        (globalCandidateAChartRealizationOfDenseCoreBound period hPeriod
          configuration data analysis chart sameAction) 0
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  apply globalCandidateANonlinearHilbertHessian_smooth_eq_covariant period
    hPeriod configuration data analysis chart sameAction
  intro core
  exact globalCandidateAChartRealizationOfDenseCoreBound_smooth period hPeriod
    configuration data analysis chart sameAction chartBound core

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreChartRealization4D
end JanusFormal
