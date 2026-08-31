import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalMaxwellGaugeCrossBlockDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D

/-!
# Robin normal-slot cross-block decomposition in the minimal physical chart

The authentic GHY/Robin block is isolated from the coupled normal equation.
Under the existing H10 action-level projection contract, its first variation
at the chart base point is the pullback of the genuine H10 first variation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)
private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance robinBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance robinBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

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

/-- The authentic non-null GHY/Robin member of the nine-block action. -/
def globalCandidateAMinimalPhysicalRobinBlockAction :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model → Real :=
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin

/-- On the admissible domain, the selected block is the exact covariant GHY
action of the chart datum. -/
theorem globalCandidateAMinimalPhysicalRobinBlockAction_eq_covariant_of_mem
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    globalCandidateAMinimalPhysicalRobinBlockAction period hPeriod
        configuration data analysis chartData point =
      globalCandidateAGHYAction period hPeriod
        ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.datumAt point hPoint).2 := by
  classical
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  have hDatum :
      chart.family.datumAtTotal period hPeriod (0 : chart.Model)
          chart.zero_mem_domain point =
        chart.family.datumAt point hPoint := by
    rw [GlobalCandidateALocalActionFamily.datumAtTotal_of_mem]
  change
    globalCandidateAGHYAction period hPeriod
        (chart.family.datumAtTotal period hPeriod (0 : chart.Model)
          chart.zero_mem_domain point).2 =
      globalCandidateAGHYAction period hPeriod
        (chart.family.datumAt point hPoint).2
  rw [hDatum]

/-- The authentic Robin block is `C²` at every admissible chart point. -/
theorem globalCandidateAMinimalPhysicalRobinBlockAction_contDiffAt_two
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalRobinBlockAction period hPeriod
        configuration data analysis chartData) point := by
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  have hC2 := fullCoupledC2WithinAt_toAt
    (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  exact hC2.robin

/-- Frechet Euler covector of the authentic Robin block alone. -/
noncomputable def globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalRobinBlockAction period hPeriod
      configuration data analysis chartData) point

/-- Pure normal directions embedded in the minimal chart. -/
def globalCandidateAMinimalPhysicalNormalChartDirection :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
    configuration data analysis chartData).comp
      (globalMinimalPhysicalNormalTestInclusion period hPeriod)

/-- Restriction of the authentic Robin covector to pure normal directions. -/
def globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt period hPeriod
    configuration data analysis chartData point).toLinearMap.comp
      (globalCandidateAMinimalPhysicalNormalChartDirection period hPeriod
        configuration data analysis chartData)

/-- Contribution of the other eight action blocks to the coupled normal
equation. -/
def globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
      hPeriod configuration data analysis chartData point

/-- Exact decomposition of the coupled normal equation. -/
theorem globalCandidateAMinimalPhysicalNormalEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt
  abel

/-- The cross-block covector is exactly the obstruction to the isolated Robin
normal equation. -/
theorem globalCandidateAMinimalPhysicalNormalEuler_eq_robinBlock_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

/-! ## H10 first-variation pullback at the chart base point -/

variable
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
      einsteinScale)

include hTransverse

/-- The Robin block's first variation at the chart base point is the pullback
of the genuine H10 boundary first variation. -/
theorem globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt_base_eq_h10Pullback :
    globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint =
      (fderiv Real
        (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric) 0).comp
        projection.localProjection := by
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let sameAction :=
    globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
      configuration data analysis chartData
  let fiberAction :=
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale data.plusGravity.metric
  have hAction :
      globalCandidateAMinimalPhysicalRobinBlockAction period hPeriod
          configuration data analysis chartData =
        fun state => fiberAction (projection.localProjection state) := by
    exact projection.robinAction_eq
  have hFiberC2 : ContDiffAt Real 2 fiberAction 0 :=
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
      period hPeriod einsteinScale data.plusGravity.metric hTransverse
  have hFiber :
      HasFDerivAt fiberAction (fderiv Real fiberAction 0) 0 :=
    (hFiberC2.differentiableAt (by norm_num)).hasFDerivAt
  have hFiberAt :
      HasFDerivAt fiberAction (fderiv Real fiberAction 0)
        (projection.localProjection sameAction.chartBridge.basePoint) := by
    rw [projection.localProjection_base_zero]
    exact hFiber
  have hPullback := hFiberAt.comp sameAction.chartBridge.basePoint
    projection.localProjection.hasFDerivAt
  unfold globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt
  rw [hAction]
  exact hPullback.fderiv

/-- At the base point, the full normal equation is the authentic H10 first
variation plus the explicit cross-block remainder. -/
theorem globalCandidateAMinimalPhysicalNormalEuler_eq_h10FirstVariation_add_crossBlock
    (variation : GlobalMinimalPhysicalNormalTest period hPeriod) :
    globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        variation =
      fderiv Real
          (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period
            hPeriod einsteinScale data.plusGravity.metric) 0
          (projection.localProjection
            (globalCandidateAMinimalPhysicalNormalChartDirection period hPeriod
              configuration data analysis chartData variation)) +
        globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData).chartBridge.basePoint
          variation := by
  rw [LinearMap.congr_fun
    (globalCandidateAMinimalPhysicalNormalEulerCovector_decomposition period
      hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.basePoint) variation]
  change
    globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData _
        (globalCandidateAMinimalPhysicalNormalChartDirection period hPeriod
          configuration data analysis chartData variation) + _ = _
  rw [globalCandidateAMinimalPhysicalRobinBlockEulerCovectorAt_base_eq_h10Pullback
    period hPeriod configuration data analysis chartData einsteinScale
      hTransverse projection]
  rfl

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D
end JanusFormal
