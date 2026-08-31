import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D

/-!
# Reduced dense-core closure from one norm identity

For a reduced Hilbert chart, completeness of the chart model and density of
the quotient core are automatic.  Thus the only remaining closure obligation
is preservation of the reduced Hilbert norm on the quotient smooth core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreClosureOfHilbertChart4D

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D

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

local instance reducedClosureCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedClosureCommonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedClosureCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedClosureCommonInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance reducedClosureCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedClosureCommonNormedSpace period hPeriod configuration data
    analysis).toModule

local instance reducedClosureCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Completeness is transported across the reduced continuous linear
equivalence; it is not an independent closure hypothesis. -/
@[reducible] def globalCandidateAMinimalPhysicalReducedChartComplete_of_hilbertChart
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData) :
    CompleteSpace
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (completeSpace_congr
    (e := reducedChart.toChart.toLinearEquiv.toEquiv)
    reducedChart.toChart.isUniformEmbedding).mp inferInstance

/-- The quotient core remains dense after applying the reduced Hilbert-chart
equivalence. -/
theorem globalCandidateAMinimalPhysicalReducedCoreToChart_denseRange_of_hilbertChart
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData) :
    DenseRange
      (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData) := by
  have hDense : DenseRange
      (reducedChart.toChart ∘
        globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis) :=
    reducedChart.toChart.surjective.denseRange.comp
      (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_denseRange
        period hPeriod configuration data analysis)
      reducedChart.toChart.continuous
  have hFunctions :
      reducedChart.toChart ∘
          globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis =
        globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData := by
    funext core
    exact reducedChart.quotient_core_compatibility core
  rw [← hFunctions]
  exact hDense

/-- Once a reduced Hilbert chart is given, norm preservation on the quotient
core is the sole remaining datum needed for the full dense-core closure. -/
def globalCandidateAMinimalPhysicalReducedDenseCoreClosure_of_hilbertChart
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)
    (norm_compatibility :
      ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
          configuration data analysis,
        ‖reducedChart.toChart
            (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
              period hPeriod configuration data analysis core)‖ =
          ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis core‖) :
    ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D period
      hPeriod configuration data analysis chartData where
  chartComplete :=
    globalCandidateAMinimalPhysicalReducedChartComplete_of_hilbertChart period
      hPeriod configuration data analysis chartData reducedChart
  norm_compatibility := by
    intro core
    rw [← reducedChart.quotient_core_compatibility core]
    exact norm_compatibility core
  dense_range :=
    globalCandidateAMinimalPhysicalReducedCoreToChart_denseRange_of_hilbertChart
      period hPeriod configuration data analysis chartData reducedChart

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreClosureOfHilbertChart4D
end JanusFormal
