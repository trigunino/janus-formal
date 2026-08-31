import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D

/-!
# Einstein--Maxwell metric-slot decomposition in the minimal physical chart

Both Einstein--Hilbert and both Maxwell action members are kept together when
restricting to metric directions, so the Maxwell metric response is not lost.
The remaining five action members form an explicit cross-block covector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D

set_option autoImplicit false

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
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

/-- The two Einstein--Hilbert and two Maxwell members of the exact action. -/
def globalCandidateAMinimalPhysicalEinsteinMaxwellBlockAction :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model → Real :=
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod (0 : chart.Model)
      chart.zero_mem_domain) measure
  fun point =>
    blocks.einsteinHilbertPlus point + blocks.einsteinHilbertMinus point +
      (blocks.maxwellPlus point + blocks.maxwellMinus point)

/-- On the admissible domain, this is exactly the covariant
Einstein--Hilbert plus Maxwell action. -/
theorem globalCandidateAMinimalPhysicalEinsteinMaxwellBlockAction_eq_covariant_of_mem
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    globalCandidateAMinimalPhysicalEinsteinMaxwellBlockAction period hPeriod
        configuration data analysis chartData point =
      globalCandidateAEinsteinHilbertAction period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.datumAt point hPoint).2
          measure +
        globalCandidateAMaxwellAction period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.datumAt point hPoint).2
          measure := by
  classical
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  have hDatum :
      chart.family.datumAtTotal period hPeriod (0 : chart.Model)
          chart.zero_mem_domain point =
        chart.family.datumAt point hPoint := by
    rw [GlobalCandidateALocalActionFamily.datumAtTotal_of_mem]
  change
    globalCandidateAEinsteinHilbertAction period hPeriod
          (chart.family.datumAtTotal period hPeriod (0 : chart.Model)
            chart.zero_mem_domain point).2 measure +
        globalCandidateAMaxwellAction period hPeriod
          (chart.family.datumAtTotal period hPeriod (0 : chart.Model)
            chart.zero_mem_domain point).2 measure = _
  rw [hDatum]

/-- The authentic Einstein--Maxwell block is `C²` at every admissible chart
point. -/
theorem globalCandidateAMinimalPhysicalEinsteinMaxwellBlockAction_contDiffAt_two
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalEinsteinMaxwellBlockAction period hPeriod
        configuration data analysis chartData) point := by
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  have hC2 := fullCoupledC2WithinAt_toAt
    (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  exact (hC2.einsteinHilbertPlus.add hC2.einsteinHilbertMinus).add
    (hC2.maxwellPlus.add hC2.maxwellMinus)

/-- Frechet Euler covector of the Einstein--Maxwell block alone. -/
noncomputable def globalCandidateAMinimalPhysicalEinsteinMaxwellBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalEinsteinMaxwellBlockAction period hPeriod
      configuration data analysis chartData) point

/-- Pure metric directions embedded in the minimal chart. -/
def globalCandidateAMinimalPhysicalMetricChartDirection :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
    configuration data analysis chartData).comp
      (globalMinimalPhysicalMetricTestInclusion period hPeriod)

/-- Restriction of the Einstein--Maxwell covector to pure metric directions. -/
def globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalEinsteinMaxwellBlockEulerCovectorAt period
    hPeriod configuration data analysis chartData point).toLinearMap.comp
      (globalCandidateAMinimalPhysicalMetricChartDirection period hPeriod
        configuration data analysis chartData)

/-- Metric response of the other five exact action members. -/
def globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
      period hPeriod configuration data analysis chartData point

/-- Exact decomposition of the coupled metric equation. -/
theorem globalCandidateAMinimalPhysicalMetricEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
          period hPeriod configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt
  abel

/-- The cross-block term is exactly the obstruction to the isolated
Einstein--Maxwell metric equation. -/
theorem globalCandidateAMinimalPhysicalMetricEuler_eq_einsteinMaxwellBlock_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
          period hPeriod configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D
end JanusFormal
