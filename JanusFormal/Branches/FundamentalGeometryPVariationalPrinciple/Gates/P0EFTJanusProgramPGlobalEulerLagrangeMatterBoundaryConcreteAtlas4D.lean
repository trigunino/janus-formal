import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeBoundaryConcreteAtlas4D

/-!
# Concrete matter-boundary variational atlas

The finite SpinC matter chart extended by null-normalization parameters has a
concrete atlas on the matter image.  Affine fiber transitions remove the
non-unique normalization representatives, while criticality remains exactly
the finite matter graph Euler equation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterBoundaryConcreteAtlas4D

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
open P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D

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

/-- Concrete atlas of the matter chart with all null-normalization fibers. -/
def globalCandidateAMatterBoundaryReparametrizationVariationalAtlas
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure := by
  let chart := globalCandidateAMatterBoundaryReparametrizationVariationalChart
    period hPeriod data measure
  let localChart := globalCandidateAVariationalChartToLocal
    period hPeriod chart
  have hLocalAction :
      globalCandidateALocalActionPullback period hPeriod localChart =
        fun state => globalCandidateAMatterFiniteGraphPulledAction
          period hPeriod data measure state.1 := by
    rw [globalCandidateAVariationalChart_toLocal_actionPullback_eq]
    exact globalCandidateAMatterBoundaryReparametrization_actionPullback_eq
      period hPeriod data measure
  exact
    { Index := Unit
      chart := fun _ => localChart
      carrier := Set.range fun core =>
        globalCandidateAMatterFiniteGraphConfiguration period hPeriod
          configuration couplings.matterMassSquared core
      cover := by
        rintro represented ⟨core, rfl⟩
        exact ⟨(), (core, 0), Set.mem_univ _, rfl⟩
      transition := by
        intro _ _ firstPoint secondPoint _ _ hSame
        change
          (GlobalCandidateAMatterFiniteGraphCore period hPeriod
              couplings.matterMassSquared ×
            GlobalCandidateABoundaryReparametrizationHilbert NullFace)
          at firstPoint secondPoint
        change globalCandidateAMatterFiniteGraphConfiguration period hPeriod
            configuration couplings.matterMassSquared firstPoint.1 =
          globalCandidateAMatterFiniteGraphConfiguration period hPeriod
            configuration couplings.matterMassSquared secondPoint.1 at hSame
        have hCore :=
          globalCandidateAMatterFiniteGraphConfiguration_injective
            period hPeriod configuration couplings.matterMassSquared hSame
        let displacement := secondPoint.2 - firstPoint.2
        exact
          { first_mem_domain := Set.mem_univ _
            second_mem_domain := Set.mem_univ _
            toFun := fun point :
                GlobalCandidateAMatterFiniteGraphCore period hPeriod
                    couplings.matterMassSquared ×
                  GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
              point + (0, displacement)
            derivative := ContinuousLinearEquiv.refl Real
              (GlobalCandidateAMatterFiniteGraphCore period hPeriod
                  couplings.matterMassSquared ×
                GlobalCandidateABoundaryReparametrizationHilbert NullFace)
            maps_point := by
              change firstPoint + (0, displacement) = secondPoint
              ext
              · simpa using hCore
              · dsimp [displacement]
                abel
            hasFDerivAt := by
              have hAffine : HasFDerivAt
                  (fun point :
                      GlobalCandidateAMatterFiniteGraphCore period hPeriod
                          couplings.matterMassSquared ×
                        GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
                    point + (0, displacement))
                  (ContinuousLinearMap.id Real
                    (GlobalCandidateAMatterFiniteGraphCore period hPeriod
                        couplings.matterMassSquared ×
                      GlobalCandidateABoundaryReparametrizationHilbert NullFace))
                  firstPoint :=
                (ContinuousLinearMap.id Real
                  (GlobalCandidateAMatterFiniteGraphCore period hPeriod
                      couplings.matterMassSquared ×
                    GlobalCandidateABoundaryReparametrizationHilbert NullFace))
                  |>.hasFDerivAt.add_const (0, displacement)
              apply hAffine.congr_fderiv
              rfl
            action_eventuallyEq := Filter.Eventually.of_forall fun point => by
              change
                (GlobalCandidateAMatterFiniteGraphCore period hPeriod
                    couplings.matterMassSquared ×
                  GlobalCandidateABoundaryReparametrizationHilbert NullFace)
                at point
              rw [hLocalAction]
              change globalCandidateAMatterFiniteGraphPulledAction
                  period hPeriod data measure point.1 =
                globalCandidateAMatterFiniteGraphPulledAction
                  period hPeriod data measure (point.1 + 0)
              rw [add_zero] } }

/-- Euler covector of the combined chart: the matter graph covector composed
with the first projection. -/
theorem globalCandidateAMatterBoundaryReparametrization_euler_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (state : GlobalCandidateAMatterFiniteGraphCore period hPeriod
        couplings.matterMassSquared ×
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalEulerLagrangeOperator period hPeriod
        (globalCandidateAMatterBoundaryReparametrizationVariationalChart
          period hPeriod data measure) state =
      (globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared state.1).comp
          (ContinuousLinearMap.fst Real
            (GlobalCandidateAMatterFiniteGraphCore period hPeriod
              couplings.matterMassSquared)
            (GlobalCandidateABoundaryReparametrizationHilbert NullFace)) := by
  let projection := ContinuousLinearMap.fst Real
    (GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared)
    (GlobalCandidateABoundaryReparametrizationHilbert NullFace)
  have hDerivative :=
    (globalCandidateAMatterFiniteGraphPulledAction_hasFDerivAt
      period hPeriod data measure state.1).comp state projection.hasFDerivAt
  unfold globalEulerLagrangeOperator actionGradient
  rw [globalCandidateAMatterBoundaryReparametrization_actionPullback_eq]
  exact hDerivative.fderiv

/-- Combined Euler vanishing is independent of the normalization coordinate
and equivalent to the finite matter graph equation. -/
theorem globalCandidateAMatterBoundaryReparametrization_euler_eq_zero_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (state : GlobalCandidateAMatterFiniteGraphCore period hPeriod
        couplings.matterMassSquared ×
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalEulerLagrangeOperator period hPeriod
        (globalCandidateAMatterBoundaryReparametrizationVariationalChart
          period hPeriod data measure) state = 0 ↔
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared state.1 = 0 := by
  rw [globalCandidateAMatterBoundaryReparametrization_euler_eq
    period hPeriod data measure state]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro direction
    change (globalCandidateAMatterFiniteGraphHessian period hPeriod
      couplings.matterMassSquared state.1) direction = 0
    have hApply := congrArg (fun map => map (direction, 0)) h
    change (globalCandidateAMatterFiniteGraphHessian period hPeriod
      couplings.matterMassSquared state.1) direction = 0 at hApply
    exact hApply
  · intro h
    rw [h]
    simp
    rfl

/-- Descended criticality on the combined concrete atlas is exactly the
finite matter equation, for every normalization representative. -/
theorem globalCandidateAMatterBoundaryReparametrizationAtlas_isEulerCritical_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    (globalCandidateAMatterBoundaryReparametrizationVariationalAtlas
        period hPeriod data measure).IsEulerCritical period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core) ↔
      globalCandidateAMatterFiniteGraphHessian period hPeriod
        couplings.matterMassSquared core = 0 := by
  let chart := globalCandidateAMatterBoundaryReparametrizationVariationalChart
    period hPeriod data measure
  let atlas := globalCandidateAMatterBoundaryReparametrizationVariationalAtlas
    period hPeriod data measure
  have hPoint : (core, parameters) ∈
      (atlas.chart ()).family.domain := Set.mem_univ _
  have hRepresents : atlas.Represents period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core)
      () (core, parameters) hPoint := rfl
  rw [atlas.isEulerCritical_iff period hPeriod _ () (core, parameters)
    hPoint hRepresents]
  change globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAVariationalChartToLocal period hPeriod chart)
      (core, parameters) = 0 ↔ _
  rw [globalCandidateAVariationalChart_toLocal_euler_eq]
  exact globalCandidateAMatterBoundaryReparametrization_euler_eq_zero_iff
    period hPeriod data measure (core, parameters)

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterBoundaryConcreteAtlas4D
end JanusFormal
