import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

/-!
# Minimal-physical variational atlas

An injective admissible local chart gives a singleton atlas on its physical
image.  Applying this to the corrected minimal-physical chart isolates the
remaining geometric input: injectivity of its configuration family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlas4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

universe u

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

/-- The physical configuration represented by an admissible local-chart
point. -/
def localChartConfigurationAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    { point : chart.Model // point ∈ chart.family.domain } →
      GlobalFieldConfiguration period hPeriod :=
  fun point => (chart.family.datumAt point.1 point.2).1

/-- Any local chart injective on its admissible domain yields a genuine
singleton atlas on the image of that domain. -/
def injectiveLocalVariationalChartAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hInjective : Function.Injective
      (localChartConfigurationAt period hPeriod chart)) :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure where
  Index := Unit
  chart := fun _ => chart
  carrier := Set.range (localChartConfigurationAt period hPeriod chart)
  cover := by
    rintro configuration ⟨point, rfl⟩
    exact ⟨(), point.1, point.2, rfl⟩
  transition := by
    intro _ _ firstPoint secondPoint hFirst hSecond hSame
    have hPoints :
        (⟨firstPoint, hFirst⟩ :
            { point : chart.Model // point ∈ chart.family.domain }) =
          ⟨secondPoint, hSecond⟩ :=
      hInjective hSame
    have hPoint : firstPoint = secondPoint := congrArg Subtype.val hPoints
    subst secondPoint
    exact GlobalCandidateALocalVariationalChartTransitionAt.refl
      period hPeriod chart firstPoint hFirst

/-- The corrected minimal-physical chart, promoted to an atlas once its
configuration family is known to be injective. -/
def globalCandidateAMinimalPhysicalVariationalAtlas
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
    (hInjective : Function.Injective
      (localChartConfigurationAt period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData))) :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure :=
  injectiveLocalVariationalChartAtlas period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData)
    hInjective

/-- The base physical configuration belongs to the minimal-physical atlas. -/
theorem globalCandidateAMinimalPhysical_configuration_mem_atlas
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
    (hInjective : Function.Injective
      (localChartConfigurationAt period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData))) :
    configuration.physical ∈
      (globalCandidateAMinimalPhysicalVariationalAtlas period hPeriod
        configuration data analysis chartData hInjective).carrier := by
  let bridge := globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
    configuration data analysis chartData
  refine ⟨⟨bridge.basePoint, bridge.basePoint_mem⟩, ?_⟩
  exact bridge.baseConfiguration_fields

/-- At the covered base configuration, descended criticality is exactly the
Euler equation in the corrected minimal-physical chart. -/
theorem globalCandidateAMinimalPhysicalAtlas_isEulerCritical_iff
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
    (hInjective : Function.Injective
      (localChartConfigurationAt period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData))) :
    (globalCandidateAMinimalPhysicalVariationalAtlas period hPeriod
        configuration data analysis chartData hInjective).IsEulerCritical
          period hPeriod configuration.physical ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint = 0 := by
  let atlas := globalCandidateAMinimalPhysicalVariationalAtlas period hPeriod
    configuration data analysis chartData hInjective
  let bridge := globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
    configuration data analysis chartData
  exact atlas.isEulerCritical_iff period hPeriod configuration.physical ()
    bridge.basePoint bridge.basePoint_mem bridge.baseConfiguration_fields

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlas4D
end JanusFormal
