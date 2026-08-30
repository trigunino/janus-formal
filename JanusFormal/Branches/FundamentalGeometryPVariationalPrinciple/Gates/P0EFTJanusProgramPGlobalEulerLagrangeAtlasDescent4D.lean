import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D

/-!
# Atlas descent of the global Euler--Lagrange equation

This gate isolates the exact atlas contract still required by `T03` and proves
that, once it is instantiated, Euler criticality is a well-defined predicate
on physical configurations rather than on chart presentations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D

universe u v

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

/-- A physical variational atlas with enough overlap data to compare Euler
covectors. Its carrier makes the scope explicit; no coverage of singular
configurations is asserted. -/
structure GlobalCandidateAVariationalAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (measure : Measure (EffectiveQuotient period hPeriod)) where
  Index : Type v
  chart : Index → GlobalCandidateALocalVariationalChart.{u} period hPeriod couplings
    NonNullFace NullFace measure
  carrier : Set (GlobalFieldConfiguration period hPeriod)
  cover : ∀ configuration ∈ carrier,
    ∃ (index : Index) (point : (chart index).Model)
      (hPoint : point ∈ (chart index).family.domain),
      ((chart index).family.datumAt point hPoint).1 = configuration
  transition :
    ∀ (firstIndex secondIndex : Index)
      (firstPoint : (chart firstIndex).Model)
      (secondPoint : (chart secondIndex).Model)
      (hFirst : firstPoint ∈ (chart firstIndex).family.domain)
      (hSecond : secondPoint ∈ (chart secondIndex).family.domain),
      ((chart firstIndex).family.datumAt firstPoint hFirst).1 =
          ((chart secondIndex).family.datumAt secondPoint hSecond).1 →
        GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
          (chart firstIndex) (chart secondIndex) firstPoint secondPoint

/-- A chart point represents a given physical configuration. -/
def GlobalCandidateAVariationalAtlas.Represents
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (atlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (index : atlas.Index) (point : (atlas.chart index).Model)
    (hPoint : point ∈ (atlas.chart index).family.domain) : Prop :=
  ((atlas.chart index).family.datumAt point hPoint).1 = configuration

/-- Global Euler criticality, initially phrased using one atlas
representation. The theorem below proves independence of this choice. -/
def GlobalCandidateAVariationalAtlas.IsEulerCritical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (atlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    (configuration : GlobalFieldConfiguration period hPeriod) : Prop :=
  ∃ (index : atlas.Index) (point : (atlas.chart index).Model)
      (hPoint : point ∈ (atlas.chart index).family.domain),
    atlas.Represents period hPeriod configuration index point hPoint ∧
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (atlas.chart index) point = 0

/-- Every configuration in the atlas carrier has a local representation. -/
theorem GlobalCandidateAVariationalAtlas.exists_representation
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (atlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    {configuration : GlobalFieldConfiguration period hPeriod}
    (hConfiguration : configuration ∈ atlas.carrier) :
    ∃ (index : atlas.Index) (point : (atlas.chart index).Model)
      (hPoint : point ∈ (atlas.chart index).family.domain),
      atlas.Represents period hPeriod configuration index point hPoint :=
  atlas.cover configuration hConfiguration

/-- Euler criticality is equivalent to vanishing in any chosen
representation of the same physical configuration. -/
theorem GlobalCandidateAVariationalAtlas.isEulerCritical_iff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (atlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (index : atlas.Index) (point : (atlas.chart index).Model)
    (hPoint : point ∈ (atlas.chart index).family.domain)
    (hRepresents :
      atlas.Represents period hPeriod configuration index point hPoint) :
    atlas.IsEulerCritical period hPeriod configuration ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (atlas.chart index) point = 0 := by
  constructor
  · rintro ⟨firstIndex, firstPoint, hFirst, hFirstRepresents, hFirstEuler⟩
    have hSameConfiguration :
        ((atlas.chart firstIndex).family.datumAt firstPoint hFirst).1 =
          ((atlas.chart index).family.datumAt point hPoint).1 :=
      hFirstRepresents.trans hRepresents.symm
    have hTransition := atlas.transition firstIndex index firstPoint point
      hFirst hPoint hSameConfiguration
    exact (globalCandidateALocalEulerLagrangeOperator_eq_zero_iff
      period hPeriod hTransition).mp hFirstEuler
  · intro hEuler
    exact ⟨index, point, hPoint, hRepresents, hEuler⟩

/-- In particular, two arbitrary presentations of one physical configuration
give equivalent Euler equations. -/
theorem GlobalCandidateAVariationalAtlas.euler_eq_zero_iff_of_represents
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (atlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (firstIndex secondIndex : atlas.Index)
    (firstPoint : (atlas.chart firstIndex).Model)
    (secondPoint : (atlas.chart secondIndex).Model)
    (hFirst : firstPoint ∈ (atlas.chart firstIndex).family.domain)
    (hSecond : secondPoint ∈ (atlas.chart secondIndex).family.domain)
    (hFirstRepresents : atlas.Represents period hPeriod configuration
      firstIndex firstPoint hFirst)
    (hSecondRepresents : atlas.Represents period hPeriod configuration
      secondIndex secondPoint hSecond) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
          (atlas.chart firstIndex) firstPoint = 0 ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
          (atlas.chart secondIndex) secondPoint = 0 := by
  rw [← atlas.isEulerCritical_iff period hPeriod configuration firstIndex
    firstPoint hFirst hFirstRepresents]
  exact atlas.isEulerCritical_iff period hPeriod configuration secondIndex
    secondPoint hSecond hSecondRepresents

end
end P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
end JanusFormal
