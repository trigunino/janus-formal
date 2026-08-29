import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNoether4D

/-!
# Nonlinear global Helmholtz reconstruction for Candidate A

The exact global Euler one-form is the Fréchet gradient of the exact assembled
action on every regular variational chart.  Its genuine Jacobian is symmetric.
The radial Poincaré primitive reconstructs the same action, and normalization
at one base configuration removes the additive constant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHelmholtzReconstruction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusConvexHelmholtzReconstruction

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

/-- The actual global Euler one-form is differentiable on every regular
variational chart. -/
theorem globalEulerLagrangeOperator_differentiable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    Differentiable Real
      (globalEulerLagrangeOperator period hPeriod chart) := by
  have hAction :=
    globalCandidateAActionPullback_contDiff_two period hPeriod chart
  have hAction' :
      ContDiff Real ((1 : WithTop ℕ∞) + 1)
        (globalCandidateAActionPullback period hPeriod chart) := by
    convert hAction using 1
    norm_num
  have hDerivative :
      ContDiff Real 1
        (fderiv Real
          (globalCandidateAActionPullback period hPeriod chart)) := by
    exact
      ((contDiff_succ_iff_fderiv (n := (1 : WithTop ℕ∞))).1
        hAction').2.2
  exact hDerivative.differentiable (by norm_num)

/-- Genuine nonlinear Helmholtz symmetry of the complete Euler Jacobian. -/
theorem globalCandidateA_nonlinearHelmholtz
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration) :
    HelmholtzJacobianAt
      (globalEulerLagrangeOperator period hPeriod chart)
      configuration := by
  exact action_gradient_helmholtz_at
    (globalCandidateAActionPullback period hPeriod chart) configuration
    (globalCandidateAActionPullback_contDiff_two period hPeriod chart
      |>.contDiffAt)

/-- Radial primitive of the actual global Euler form, normalized to the value
of the physical action at the selected base configuration. -/
noncomputable def globalCandidateAReconstructedAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (base configuration : chart.Configuration) : Real :=
  radialAction base
      (globalEulerLagrangeOperator period hPeriod chart) configuration +
    globalCandidateAActionPullback period hPeriod chart base

/-- The reconstructed action has exactly the global Euler derivative. -/
theorem globalCandidateAReconstructedAction_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (base configuration : chart.Configuration) :
    HasFDerivAt
      (globalCandidateAReconstructedAction period hPeriod chart base)
      (globalEulerLagrangeOperator period hPeriod chart configuration)
      configuration := by
  change HasFDerivAt
    (fun point =>
      radialAction base
          (globalEulerLagrangeOperator period hPeriod chart) point +
        globalCandidateAActionPullback period hPeriod chart base)
    (globalEulerLagrangeOperator period hPeriod chart configuration)
    configuration
  exact
    (radial_action_hasFDerivAt
      (globalEulerLagrangeOperator period hPeriod chart)
      (globalEulerLagrangeOperator_differentiable period hPeriod chart)
      (globalCandidateA_nonlinearHelmholtz period hPeriod chart)
      base configuration).add_const _

@[simp]
theorem globalCandidateAReconstructedAction_at_base
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (base : chart.Configuration) :
    globalCandidateAReconstructedAction period hPeriod chart base base =
      globalCandidateAActionPullback period hPeriod chart base := by
  simp [globalCandidateAReconstructedAction]

/-- Exact reconstruction: normalization at one point identifies the radial
primitive with the original global Candidate-A action everywhere. -/
theorem globalCandidateAReconstructedAction_eq_original
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (base : chart.Configuration) :
    globalCandidateAReconstructedAction period hPeriod chart base =
      globalCandidateAActionPullback period hPeriod chart := by
  funext configuration
  have hEqOn :=
    convex_actions_same_euler_eqOn_of_eq_at_base
      (domain := Set.univ)
      (euler := globalEulerLagrangeOperator period hPeriod chart)
      (firstAction :=
        globalCandidateAReconstructedAction period hPeriod chart base)
      (secondAction :=
        globalCandidateAActionPullback period hPeriod chart)
      convex_univ
      (by
        intro point _
        exact globalCandidateAReconstructedAction_hasFDerivAt
          period hPeriod chart base point)
      (by
        intro point _
        exact globalCandidateAAction_hasFDerivAt
          period hPeriod chart point)
      (Set.mem_univ base)
      (globalCandidateAReconstructedAction_at_base
        period hPeriod chart base)
  exact hEqOn (Set.mem_univ configuration)

/-- Any other action on the same chart with the same actual Euler one-form
differs from Candidate A by one additive constant. -/
theorem globalCandidateA_sameEuler_differ_by_constant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (otherAction : chart.Configuration → Real)
    (hOther : ∀ configuration,
      HasFDerivAt otherAction
        (globalEulerLagrangeOperator period hPeriod chart configuration)
        configuration) :
    ∃ constant : Real, ∀ configuration,
      otherAction configuration =
        globalCandidateAActionPullback period hPeriod chart configuration +
          constant := by
  simpa using
    (convex_actions_same_euler_differ_by_constant
      (domain := Set.univ)
      (euler := globalEulerLagrangeOperator period hPeriod chart)
      (firstAction := otherAction)
      (secondAction :=
        globalCandidateAActionPullback period hPeriod chart)
      convex_univ Set.univ_nonempty
      (by intro configuration _; exact hOther configuration)
      (by
        intro configuration _
        exact globalCandidateAAction_hasFDerivAt
          period hPeriod chart configuration))

/-- Global nonlinear Helmholtz and exact-action reconstruction gate. -/
theorem global_helmholtz_reconstruction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (base : chart.Configuration) :
    (∀ configuration,
      HelmholtzJacobianAt
        (globalEulerLagrangeOperator period hPeriod chart)
        configuration) ∧
      (∀ configuration,
        HasFDerivAt
          (globalCandidateAReconstructedAction period hPeriod chart base)
          (globalEulerLagrangeOperator period hPeriod chart configuration)
          configuration) ∧
      globalCandidateAReconstructedAction period hPeriod chart base =
        globalCandidateAActionPullback period hPeriod chart := by
  exact ⟨globalCandidateA_nonlinearHelmholtz period hPeriod chart,
    globalCandidateAReconstructedAction_hasFDerivAt
      period hPeriod chart base,
    globalCandidateAReconstructedAction_eq_original
      period hPeriod chart base⟩

end
end P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
end JanusFormal
