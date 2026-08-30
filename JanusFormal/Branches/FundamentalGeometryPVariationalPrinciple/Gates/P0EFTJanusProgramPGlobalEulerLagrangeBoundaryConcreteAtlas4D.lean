import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D

/-!
# Concrete boundary-reparametrization variational atlas

A constant-action whole-space chart yields a singleton-carrier atlas whose
different chart representatives are related by explicit affine translations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeBoundaryConcreteAtlas4D

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
open P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D

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
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- A constant-action whole-space chart gives an atlas on its single physical
configuration, with explicit translations between all representatives. -/
def constantGlobalVariationalChartAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (hConfiguration : ∀ point,
      chart.family.configurationAt point = configuration)
    (constant : Real)
    (hAction : globalCandidateAActionPullback period hPeriod chart =
      fun _ => constant) :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure := by
  let localChart := globalCandidateAVariationalChartToLocal
    period hPeriod chart
  have hLocalAction :
      globalCandidateALocalActionPullback period hPeriod localChart =
        fun _ => constant := by
    rw [globalCandidateAVariationalChart_toLocal_actionPullback_eq]
    exact hAction
  exact
    { Index := Unit
      chart := fun _ => localChart
      carrier := {configuration}
      cover := by
        intro represented hRepresented
        have hEq : represented = configuration :=
          Set.mem_singleton_iff.mp hRepresented
        subst represented
        exact ⟨(), 0, Set.mem_univ 0, hConfiguration 0⟩
      transition := by
        intro _ _ firstPoint secondPoint hFirst hSecond _
        let displacement := secondPoint - firstPoint
        exact
          { first_mem_domain := hFirst
            second_mem_domain := hSecond
            toFun := fun point => point + displacement
            derivative := ContinuousLinearEquiv.refl Real localChart.Model
            maps_point := by
              dsimp [displacement]
              abel
            hasFDerivAt := by
              have hAffine : HasFDerivAt
                  (fun point : localChart.Model => point + displacement)
                  (ContinuousLinearMap.id Real localChart.Model) firstPoint :=
                (ContinuousLinearMap.id Real localChart.Model).hasFDerivAt.add_const
                  displacement
              simpa using hAffine
            action_eventuallyEq := Filter.Eventually.of_forall fun point => by
              rw [hLocalAction]
              rfl } }

/-- Concrete atlas of all null-normalization representatives of one physical
configuration. -/
def globalCandidateABoundaryReparametrizationVariationalAtlas
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
  constantGlobalVariationalChartAtlas period hPeriod
    (globalCandidateABoundaryReparametrizationVariationalChart
      period hPeriod data measure)
    configuration
    (globalCandidateABoundaryReparametrizationActionFamily_configurationAt
      period hPeriod data)
    (globalCandidateACovariantAction period hPeriod data measure)
    (globalCandidateABoundaryReparametrization_actionPullback_eq
      period hPeriod data measure)

/-- The true Euler covector vanishes at every boundary-normalization
representative. -/
theorem globalCandidateABoundaryReparametrization_euler_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalEulerLagrangeOperator period hPeriod
        (globalCandidateABoundaryReparametrizationVariationalChart
          period hPeriod data measure) parameters = 0 := by
  unfold globalEulerLagrangeOperator actionGradient
  rw [globalCandidateABoundaryReparametrization_actionPullback_eq]
  apply ContinuousLinearMap.ext
  intro direction
  simp
  change (0 : Real) = 0
  rfl

/-- The single physical configuration carried by the concrete boundary atlas
is Euler critical. -/
theorem globalCandidateABoundaryReparametrizationAtlas_isEulerCritical
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateABoundaryReparametrizationVariationalAtlas
      period hPeriod data measure).IsEulerCritical period hPeriod
        configuration := by
  let chart := globalCandidateABoundaryReparametrizationVariationalChart
    period hPeriod data measure
  let atlas := globalCandidateABoundaryReparametrizationVariationalAtlas
    period hPeriod data measure
  have hPoint : (0 : chart.Configuration) ∈
      (atlas.chart ()).family.domain := Set.mem_univ 0
  have hRepresents : atlas.Represents period hPeriod configuration () 0 hPoint :=
    rfl
  rw [atlas.isEulerCritical_iff period hPeriod configuration () 0
    hPoint hRepresents]
  change globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAVariationalChartToLocal period hPeriod chart) 0 = 0
  rw [globalCandidateAVariationalChart_toLocal_euler_eq]
  exact globalCandidateABoundaryReparametrization_euler_eq_zero
    period hPeriod data measure 0

end
end P0EFTJanusProgramPGlobalEulerLagrangeBoundaryConcreteAtlas4D
end JanusFormal
