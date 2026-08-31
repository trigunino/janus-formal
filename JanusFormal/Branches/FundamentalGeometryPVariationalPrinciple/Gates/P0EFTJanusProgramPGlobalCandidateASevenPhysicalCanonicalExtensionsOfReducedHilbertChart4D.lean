import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D

/-!
# Canonical H11 extensions from the reduced Hilbert chart

Unlike the obstructed augmented common chart, the reduced Hilbert chart sees
the quotient core faithfully.  Its operator norm, composed with orthogonal
Hilbert reduction, bounds the original smooth core-to-chart map and therefore
constructs all seven canonical H11 extensions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D
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
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)

local instance commonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance commonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance commonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (commonInnerProductSpace period hPeriod configuration data analysis).toNormedSpace

local instance commonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (commonNormedSpace period hPeriod configuration data analysis).toModule

include reducedChart in
/-- The reduced chart supplies the honest smooth-core estimate. -/
def globalCandidateASevenPhysicalCanonicalCoreToChartBound_of_reducedHilbertChart :
    GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) := by
  let reduction := globalCandidateAMinimalPhysicalHilbertReduction period
    hPeriod configuration data analysis
  let chartRealization := reducedChart.toChart.toContinuousLinearMap
  exact
    { constant := ‖chartRealization‖ * ‖reduction‖
      constant_nonneg :=
        mul_nonneg (norm_nonneg chartRealization) (norm_nonneg reduction)
      estimate := by
        intro core
        change
          ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration
              data analysis
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData)
              (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
                hPeriod configuration data analysis chartData) core‖ ≤
            (‖chartRealization‖ * ‖reduction‖) *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis core‖
        rw [← globalCandidateAMinimalPhysicalReducedCoreToChart_mk period
          hPeriod configuration data analysis chartData core]
        rw [← reducedChart.quotient_core_compatibility
          (Submodule.Quotient.mk core)]
        rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
        change
          ‖chartRealization
              (reduction
                (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                  configuration data analysis core))‖ ≤
            (‖chartRealization‖ * ‖reduction‖) *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis core‖
        calc
          _ ≤ ‖chartRealization‖ *
              ‖reduction
                (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                  configuration data analysis core)‖ :=
            chartRealization.le_opNorm _
          _ ≤ ‖chartRealization‖ *
              (‖reduction‖ *
                ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                  configuration data analysis core‖) :=
            mul_le_mul_of_nonneg_left (reduction.le_opNorm _)
              (norm_nonneg chartRealization)
          _ = _ := by ring }

include reducedChart in
/-- Seven canonical separated H11 extensions from the reduced chart. -/
def globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_reducedHilbertChart :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_chartBound
    period hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
      (globalCandidateASevenPhysicalCanonicalCoreToChartBound_of_reducedHilbertChart
        period hPeriod configuration data analysis chartData reducedChart)

include reducedChart in
/-- Gate 200: the unobstructed reduced Hilbert chart canonically determines
all seven H11 block extensions. -/
def candidate_a_seven_physical_canonical_extensions_of_reducedHilbertChart_gate :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_reducedHilbertChart
    period hPeriod configuration data analysis chartData reducedChart

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D
end JanusFormal
