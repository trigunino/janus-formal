import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreChartRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

/-!
# Nonlinear residual atlas from the minimal physical Hilbert chart

An existing continuous linear equivalence from the common graph Hilbert space
to the corrected minimal physical chart directly supplies the bounded chart
realization required by the nonlinear Euler atlas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
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
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData))

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

/-- The existing Hilbert equivalence is the required bounded realization of
the common completion in the concrete minimal physical chart. -/
def globalCandidateAMinimalPhysicalHilbertChartRealization :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  hilbertChart.toChart.toContinuousLinearMap

/-- The realization agrees with the genuine tangent map on the dense smooth
core. -/
theorem globalCandidateAMinimalPhysicalHilbertChartRealization_smooth
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core) =
      globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) core := by
  exact hilbertChart.smooth_core_compatibility core

/-- Its operator norm supplies the graph-norm estimate, so no independent
dense-core bound is needed. -/
def globalCandidateAMinimalPhysicalHilbertChartBound : @DenseCoreChartMapBound
    (GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis)
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model
    inferInstance inferInstance
    (commonAugmentedNormedAddCommGroup period hPeriod configuration data
      analysis)
    (commonAugmentedNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).normedAddCommGroup
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).normedSpace
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
        →ₗ[Real] CommonAugmentedHilbert period hPeriod configuration data
          analysis)
    (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
      analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)) where
  constant := ‖globalCandidateAMinimalPhysicalHilbertChartRealization period
    hPeriod configuration data analysis chartData hilbertChart‖
  constant_nonneg := norm_nonneg _
  estimate := by
    intro core
    rw [← globalCandidateAMinimalPhysicalHilbertChartRealization_smooth period
      hPeriod configuration data analysis chartData hilbertChart core]
    exact
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart).le_opNorm _

/-- Concrete singleton nonlinear residual atlas for the selected minimal
physical Hilbert chart. -/
def globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas :
    GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis :=
  GlobalCandidateANonlinearHilbertResidualAtlas.singleton period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData)
    (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
      configuration data analysis chartData).chartBridge.basePoint
    (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
      configuration data analysis chartData hilbertChart)

/-- Its nonlinear linearization is the genuine covariant Hessian on the
smooth core. -/
theorem globalCandidateAMinimalPhysicalNonlinearHilbertHessian_smooth_eq_covariant
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart) 0
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge first second := by
  apply globalCandidateANonlinearHilbertHessian_smooth_eq_covariant period
    hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart)
  exact globalCandidateAMinimalPhysicalHilbertChartRealization_smooth period
    hPeriod configuration data analysis chartData hilbertChart

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
end JanusFormal
