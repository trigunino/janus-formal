import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

/-!
# Maxwell gauge-slot cross-block decomposition in the minimal physical chart

The two authentic covariant Maxwell members of the nine-block action are
combined before restricting their Frechet covector to pure gauge directions.
The difference from the coupled gauge equation is retained explicitly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalMaxwellGaugeCrossBlockDecomposition4D

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

/-- Sum of the two authentic Maxwell members of the nine-block action. -/
def globalCandidateAMinimalPhysicalMaxwellBlockAction :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model → Real :=
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod (0 : chart.Model)
      chart.zero_mem_domain) measure
  fun point => blocks.maxwellPlus point + blocks.maxwellMinus point

/-- On the admissible domain, this block is exactly the covariant Maxwell
action evaluated on the chart datum. -/
theorem globalCandidateAMinimalPhysicalMaxwellBlockAction_eq_covariant_of_mem
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    globalCandidateAMinimalPhysicalMaxwellBlockAction period hPeriod
        configuration data analysis chartData point =
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
    globalCandidateAMaxwellAction period hPeriod
        (chart.family.datumAtTotal period hPeriod (0 : chart.Model)
          chart.zero_mem_domain point).2 measure =
      globalCandidateAMaxwellAction period hPeriod
        (chart.family.datumAt point hPoint).2 measure
  rw [hDatum]

/-- The authentic Maxwell block is genuinely `C²` at every admissible chart
point. -/
theorem globalCandidateAMinimalPhysicalMaxwellBlockAction_contDiffAt_two
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalMaxwellBlockAction period hPeriod
        configuration data analysis chartData) point := by
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod (0 : chart.Model)
      chart.zero_mem_domain) measure
  have hC2 := fullCoupledC2WithinAt_toAt
    (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  exact hC2.maxwellPlus.add hC2.maxwellMinus

/-- Frechet Euler covector of the authentic Maxwell block alone. -/
noncomputable def globalCandidateAMinimalPhysicalMaxwellBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalMaxwellBlockAction period hPeriod
      configuration data analysis chartData) point

/-- Pure gauge directions embedded in the minimal chart. -/
def globalCandidateAMinimalPhysicalGaugeChartDirection :
    GlobalMinimalPhysicalGaugeTest period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
    configuration data analysis chartData).comp
      (globalMinimalPhysicalGaugeTestInclusion period hPeriod)

/-- Restriction of the authentic Maxwell-block covector to pure gauge
directions. -/
def globalCandidateAMinimalPhysicalMaxwellBlockGaugeEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalGaugeTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalMaxwellBlockEulerCovectorAt period hPeriod
    configuration data analysis chartData point).toLinearMap.comp
      (globalCandidateAMinimalPhysicalGaugeChartDirection period hPeriod
        configuration data analysis chartData)

/-- Contribution of the other seven action blocks to the coupled gauge
equation.  No vanishing is assumed. -/
def globalCandidateAMinimalPhysicalGaugeCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalGaugeTest period hPeriod →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalMaxwellBlockGaugeEulerCovectorAt period
      hPeriod configuration data analysis chartData point

/-- Exact decomposition of the coupled gauge equation. -/
theorem globalCandidateAMinimalPhysicalGaugeEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalMaxwellBlockGaugeEulerCovectorAt period
          hPeriod configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalGaugeCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalGaugeCrossBlockEulerCovectorAt
  abel

/-- The named cross-block term is exactly the obstruction to identifying the
coupled gauge equation with the authentic Maxwell equation. -/
theorem globalCandidateAMinimalPhysicalGaugeEuler_eq_maxwellBlock_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalMaxwellBlockGaugeEulerCovectorAt period
          hPeriod configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalGaugeCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalGaugeCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalMaxwellGaugeCrossBlockDecomposition4D
end JanusFormal
