import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D

/-!
# Concrete finite-matter variational atlas

The existing injective finite SpinC matter chart gives a genuine singleton
atlas on its physical image.  Its descended criticality equation is the exact
closed graph Euler equation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

universe u

variable (period : Real) (hPeriod : period ≠ 0)

local instance matterFiniteCoreNormedAddCommGroup (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
    period hPeriod massSquared

local instance matterFiniteCoreNormedSpace (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedSpace
    period hPeriod massSquared

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
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Any injective whole-space variational chart yields a genuine singleton
atlas on the image of its physical configuration map. -/
def injectiveGlobalVariationalChartAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hInjective : Function.Injective chart.family.configurationAt) :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure where
  Index := Unit
  chart := fun _ => globalCandidateAVariationalChartToLocal
    period hPeriod chart
  carrier := Set.range chart.family.configurationAt
  cover := by
    rintro configuration ⟨point, rfl⟩
    exact ⟨(), point, Set.mem_univ point, rfl⟩
  transition := by
    intro _ _ firstPoint secondPoint hFirst hSecond hSame
    change chart.family.configurationAt firstPoint =
      chart.family.configurationAt secondPoint at hSame
    have hPoints := hInjective hSame
    subst secondPoint
    exact GlobalCandidateALocalVariationalChartTransitionAt.refl
      period hPeriod _ firstPoint hFirst

/-- The physical configuration map of the finite matter chart is injective. -/
theorem globalCandidateAMatterFiniteGraphConfiguration_injective
    (configuration : GlobalFieldConfiguration period hPeriod)
    (massSquared : Real) :
    Function.Injective
      (globalCandidateAMatterFiniteGraphConfiguration
        period hPeriod configuration massSquared) := by
  intro first second hConfiguration
  have hMatter := congrArg GlobalFieldConfiguration.spinCMatter hConfiguration
  change programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
      ((globalCandidateAMatterFiniteGraphCoreEquiv
        period hPeriod massSquared).symm first) =
    programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
      ((globalCandidateAMatterFiniteGraphCoreEquiv
        period hPeriod massSquared).symm second) at hMatter
  have hCoefficients :=
    programPPrimitiveSpinCMatterSmoothFiniteSynthesis_injective
      period hPeriod hMatter
  exact (globalCandidateAMatterFiniteGraphCoreEquiv
    period hPeriod massSquared).symm.injective hCoefficients

/-- Concrete singleton atlas carried by the finite SpinC-matter family. -/
def globalCandidateAMatterFiniteGraphVariationalAtlas
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure :=
  injectiveGlobalVariationalChartAtlas period hPeriod
    (globalCandidateAMatterFiniteGraphVariationalChart
      period hPeriod data measure)
    (globalCandidateAMatterFiniteGraphConfiguration_injective
      period hPeriod configuration couplings.matterMassSquared)

/-- The true Euler covector of the concrete matter chart is its closed graph
Hessian applied to the chart point. -/
theorem globalCandidateAMatterFiniteGraph_euler_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalEulerLagrangeOperator period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) core =
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared core := by
  unfold globalEulerLagrangeOperator actionGradient
  rw [globalCandidateAMatterFiniteGraph_actionPullback_eq]
  exact globalCandidateAMatterFiniteGraphPulledAction_fderiv
    period hPeriod data measure core

/-- On the concrete finite-matter atlas, descended criticality is exactly the
closed graph Euler equation. -/
theorem globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    (globalCandidateAMatterFiniteGraphVariationalAtlas
        period hPeriod data measure).IsEulerCritical period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core) ↔
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared core = 0 := by
  let chart := globalCandidateAMatterFiniteGraphVariationalChart
    period hPeriod data measure
  let atlas := globalCandidateAMatterFiniteGraphVariationalAtlas
    period hPeriod data measure
  have hPoint : core ∈ (atlas.chart ()).family.domain := Set.mem_univ core
  have hRepresents : atlas.Represents period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core) () core hPoint := rfl
  rw [atlas.isEulerCritical_iff period hPeriod _ () core hPoint hRepresents]
  change globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAVariationalChartToLocal period hPeriod chart) core = 0 ↔ _
  rw [globalCandidateAVariationalChart_toLocal_euler_eq]
  rw [globalCandidateAMatterFiniteGraph_euler_eq period hPeriod data measure core]
  rfl

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D
end JanusFormal
