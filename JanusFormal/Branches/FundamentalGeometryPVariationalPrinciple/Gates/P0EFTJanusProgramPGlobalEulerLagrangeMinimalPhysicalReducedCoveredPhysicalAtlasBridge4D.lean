import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D

/-!
# Physical-atlas bridge for the covered reduced Hilbert atlas

A specialized physical variational atlas and a compatible reduced Hilbert
realization construct the covered atlas of Gate 209.  Its descended criticality
is exactly chart-independent criticality of the represented physical field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoveredPhysicalAtlasBridge4D

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlas4D

universe v

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

/-- A physical variational atlas whose members are precisely minimal physical
charts produced by a family of chart data. -/
structure GlobalCandidateAMinimalPhysicalVariationalCoveredAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  Index : Type v
  chartData : Index → ProgramPGlobalMinimalPhysicalActionChartData4D period
    hPeriod (measure := measure) configuration data analysis
  carrier : Set (GlobalFieldConfiguration period hPeriod)
  cover : ∀ physical ∈ carrier,
    ∃ (index : Index)
      (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
        hPeriod configuration data analysis (chartData index)).Model)
      (hPoint : point ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData index)).family.domain),
      ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData index)).family.datumAt point
          hPoint).1 = physical
  transition : ∀ (first second : Index)
      (firstPoint : (globalCandidateAMinimalPhysicalLocalVariationalChart
        period hPeriod configuration data analysis
          (chartData first)).Model)
      (secondPoint : (globalCandidateAMinimalPhysicalLocalVariationalChart
        period hPeriod configuration data analysis
          (chartData second)).Model)
      (hFirst : firstPoint ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData first)).family.domain)
      (hSecond : secondPoint ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (chartData second)).family.domain),
    ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData first)).family.datumAt
          firstPoint hFirst).1 =
      ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData second)).family.datumAt
          secondPoint hSecond).1 →
    GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData first))
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (chartData second)) firstPoint secondPoint

namespace GlobalCandidateAMinimalPhysicalVariationalCoveredAtlas

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (physicalAtlas : GlobalCandidateAMinimalPhysicalVariationalCoveredAtlas
      period hPeriod (measure := measure) configuration data analysis)

/-- Forgetting the specialized chart-data presentation gives the existing
physical variational-atlas API. -/
def toVariationalAtlas : GlobalCandidateAVariationalAtlas period hPeriod
    (couplings := couplings) (NonNullFace := NonNullFace)
    (NullFace := NullFace) measure where
  Index := physicalAtlas.Index
  chart := fun index ↦ globalCandidateAMinimalPhysicalLocalVariationalChart
    period hPeriod configuration data analysis (physicalAtlas.chartData index)
  carrier := physicalAtlas.carrier
  cover := physicalAtlas.cover
  transition := physicalAtlas.transition

end GlobalCandidateAMinimalPhysicalVariationalCoveredAtlas

/-- Data identifying a covered family of reduced Hilbert charts with one
physical configuration on every overlap. -/
structure GlobalCandidateAMinimalPhysicalReducedCoveredAtlasRealization
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (physicalAtlas : GlobalCandidateAMinimalPhysicalVariationalCoveredAtlas
      period hPeriod (measure := measure) configuration data analysis) where
  reducedChart : (index : physicalAtlas.Index) →
    ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period hPeriod
      configuration data analysis (physicalAtlas.chartData index)
  carrier : Set (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
    configuration data analysis)
  cover : ∀ state ∈ carrier, ∃ index : physicalAtlas.Index,
    globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData index)
          (reducedChart index) state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis
          (physicalAtlas.chartData index)).family.domain
  representedConfiguration :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
      data analysis → GlobalFieldConfiguration period hPeriod
  represented_mem : ∀ state ∈ carrier,
    representedConfiguration state ∈ physicalAtlas.carrier
  represents : ∀
      (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis) (hState : state ∈ carrier)
      (index : physicalAtlas.Index)
      (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
          hPeriod configuration data analysis (physicalAtlas.chartData index)
            (reducedChart index) state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis
            (physicalAtlas.chartData index)).family.domain),
    ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis
          (physicalAtlas.chartData index)).family.datumAt
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData index)
          (reducedChart index) state) hPoint).1 = representedConfiguration state
  derivative_compatible : ∀
      (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis) (hState : state ∈ carrier)
      (first second : physicalAtlas.Index)
      (hFirst : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
          hPeriod configuration data analysis (physicalAtlas.chartData first)
            (reducedChart first) state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis
            (physicalAtlas.chartData first)).family.domain)
      (hSecond : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
          hPeriod configuration data analysis (physicalAtlas.chartData second)
            (reducedChart second) state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis
            (physicalAtlas.chartData second)).family.domain),
    ((physicalAtlas.transition first second
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData first)
          (reducedChart first) state)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData second)
          (reducedChart second) state) hFirst hSecond
      ((represents state hState first hFirst).trans
        (represents state hState second hSecond).symm)).derivative.toContinuousLinearMap.comp
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis (physicalAtlas.chartData first)
          (reducedChart first))) =
    globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
      hPeriod configuration data analysis (physicalAtlas.chartData second)
        (reducedChart second)

namespace GlobalCandidateAMinimalPhysicalReducedCoveredAtlasRealization

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {physicalAtlas : GlobalCandidateAMinimalPhysicalVariationalCoveredAtlas
      period hPeriod (measure := measure) configuration data analysis}
    (realization : GlobalCandidateAMinimalPhysicalReducedCoveredAtlasRealization
      period hPeriod configuration data analysis physicalAtlas)

/-- The physical overlap transition constructs the covered reduced atlas. -/
def toCoveredAtlas :
    GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas period
      hPeriod (measure := measure) configuration data analysis where
  Index := physicalAtlas.Index
  chartData := physicalAtlas.chartData
  reducedChart := realization.reducedChart
  carrier := realization.carrier
  cover := realization.cover
  transition := by
    intro state hState first second hFirst hSecond
    exact physicalAtlas.transition first second
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData first)
          (realization.reducedChart first) state)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData second)
          (realization.reducedChart second) state) hFirst hSecond
      ((realization.represents state hState first hFirst).trans
        (realization.represents state hState second hSecond).symm)
  derivative_compatible := realization.derivative_compatible

/-- Every admissible reduced chart point represents the selected physical
configuration in the specialized physical atlas. -/
theorem chart_represents
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ realization.carrier)
    (index : physicalAtlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (physicalAtlas.chartData index)
          (realization.reducedChart index) state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis
          (physicalAtlas.chartData index)).family.domain) :
    (physicalAtlas.toVariationalAtlas period hPeriod).Represents period hPeriod
      (realization.representedConfiguration state) index
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData index)
          (realization.reducedChart index) state) hPoint :=
  realization.represents state hState index hPoint

/-- Covered reduced criticality is exactly chart-independent criticality of
the represented physical configuration. -/
theorem isEulerCritical_iff_physicalAtlas
    (state : (realization.toCoveredAtlas period hPeriod).carrier) :
    (realization.toCoveredAtlas period hPeriod).IsEulerCritical period hPeriod
        state ↔
      (physicalAtlas.toVariationalAtlas period hPeriod).IsEulerCritical period
        hPeriod (realization.representedConfiguration state.1) := by
  let coveredAtlas := realization.toCoveredAtlas period hPeriod
  let variationalAtlas := physicalAtlas.toVariationalAtlas period hPeriod
  let index := coveredAtlas.selectedIndex period hPeriod state
  have hPoint := coveredAtlas.selectedIndex_mem_domain period hPeriod state
  have hCovered := coveredAtlas.isEulerCritical_iff_chart_localEuler period
    hPeriod state index hPoint
  have hPhysical :
      variationalAtlas.IsEulerCritical period hPeriod
          (realization.representedConfiguration state.1) ↔
        globalCandidateALocalEulerLagrangeOperator period hPeriod
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis (physicalAtlas.chartData index))
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis (physicalAtlas.chartData index)
              (realization.reducedChart index) state.1) = 0 := by
    apply variationalAtlas.isEulerCritical_iff period hPeriod
      (realization.representedConfiguration state.1) index
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis (physicalAtlas.chartData index)
          (realization.reducedChart index) state.1) hPoint
    exact realization.chart_represents period hPeriod state.1 state.2 index
      hPoint
  exact hCovered.trans hPhysical.symm

end GlobalCandidateAMinimalPhysicalReducedCoveredAtlasRealization

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoveredPhysicalAtlasBridge4D
end JanusFormal
