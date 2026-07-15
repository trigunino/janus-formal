import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction

namespace JanusFormal
namespace P0EFTJanusNonlinearGaugeFlowNoether

set_option autoImplicit false

open P0EFTJanusConvexHelmholtzReconstruction

/-- A complete one-parameter gauge flow with a possibly field-dependent
infinitesimal generator.  The flow law and actual orbit derivative are data;
this gate does not construct a Janus gauge group. -/
structure CompleteGaugeFlow (Configuration : Type*)
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration] where
  flow : ℝ → Configuration → Configuration
  generator : Configuration → Configuration
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ first second x,
    flow (first + second) x = flow first (flow second x)
  orbit_hasDerivAt : ∀ x t,
    HasDerivAt (fun s => flow s x) (generator (flow t x)) t

/-- Invariance of an action along every orbit of a complete gauge flow. -/
def FlowGaugeInvariant
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (action : Configuration → ℝ) : Prop :=
  ∀ x t, action (gaugeFlow.flow t x) = action x

/-- Nonlinear infinitesimal Noether identity: the Euler one-form annihilates
the field-dependent gauge generator at every configuration. -/
def EulerAnnihilatesGenerator
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration) : Prop :=
  ∀ x, euler x (gaugeFlow.generator x) = 0

/-- Invariance under a differentiable nonlinear gauge flow forces the actual
Euler one-form to annihilate its field-dependent infinitesimal generator. -/
theorem euler_annihilates_generator_of_flow_gauge_invariant
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (action : Configuration → ℝ)
    (hGradient : ∀ x, HasFDerivAt action (euler x) x)
    (hInvariant : FlowGaugeInvariant gaugeFlow action) :
    EulerAnnihilatesGenerator gaugeFlow euler := by
  intro x
  let orbitAction : ℝ → ℝ := fun t => action (gaugeFlow.flow t x)
  have hOrbitDerivative :
      HasDerivAt orbitAction
        (euler x (gaugeFlow.generator x)) 0 := by
    have hComp :=
      (hGradient (gaugeFlow.flow 0 x)).comp_hasDerivAt 0
        (gaugeFlow.orbit_hasDerivAt x 0)
    simpa [orbitAction, gaugeFlow.flow_zero x, Function.comp_def] using hComp
  have hOrbitConstant : orbitAction = fun _ => action x := by
    funext t
    exact hInvariant x t
  have hZeroDerivative : HasDerivAt orbitAction 0 0 := by
    rw [hOrbitConstant]
    exact hasDerivAt_const (x := (0 : ℝ)) (c := action x)
  exact hOrbitDerivative.unique hZeroDerivative

/-- If the actual Euler one-form annihilates a complete nonlinear gauge
generator everywhere, then the action is constant along every full orbit. -/
theorem flow_gauge_invariant_of_euler_annihilates_generator
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (action : Configuration → ℝ)
    (hGradient : ∀ x, HasFDerivAt action (euler x) x)
    (hHorizontal : EulerAnnihilatesGenerator gaugeFlow euler) :
    FlowGaugeInvariant gaugeFlow action := by
  intro x t
  let orbitAction : ℝ → ℝ := fun s => action (gaugeFlow.flow s x)
  have hOrbitDerivative (s : ℝ) : HasDerivAt orbitAction 0 s := by
    have hComp :=
      (hGradient (gaugeFlow.flow s x)).comp_hasDerivAt s
        (gaugeFlow.orbit_hasDerivAt x s)
    simpa [orbitAction, Function.comp_def, hHorizontal (gaugeFlow.flow s x)]
      using hComp
  have hOrbitDifferentiable : Differentiable ℝ orbitAction :=
    fun s => (hOrbitDerivative s).differentiableAt
  have hOrbitDerivZero (s : ℝ) : deriv orbitAction s = 0 :=
    (hOrbitDerivative s).deriv
  have hConstant :=
    is_const_of_deriv_eq_zero hOrbitDifferentiable hOrbitDerivZero t 0
  simpa [orbitAction, gaugeFlow.flow_zero x] using hConstant

/-- Exact nonlinear Noether equivalence for a complete differentiable gauge
flow, conditional only on the supplied Euler one-form being the action's
actual Fréchet derivative everywhere. -/
theorem flow_gauge_invariant_iff_euler_annihilates_generator
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (action : Configuration → ℝ)
    (hGradient : ∀ x, HasFDerivAt action (euler x) x) :
    FlowGaugeInvariant gaugeFlow action ↔
      EulerAnnihilatesGenerator gaugeFlow euler := by
  constructor
  · exact euler_annihilates_generator_of_flow_gauge_invariant
      gaugeFlow euler action hGradient
  · exact flow_gauge_invariant_of_euler_annihilates_generator
      gaugeFlow euler action hGradient

/-- Combining nonlinear Helmholtz reconstruction with nonlinear Noether:
a differentiable symmetric Euler one-form that annihilates a complete gauge
generator admits a normalized action invariant under the full flow. -/
theorem normalized_flow_gauge_invariant_radial_reconstruction
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (hDifferentiable : Differentiable ℝ euler)
    (hHelmholtz : ∀ x, HelmholtzJacobianAt euler x)
    (hHorizontal : EulerAnnihilatesGenerator gaugeFlow euler)
    (base : Configuration) :
    ∃ action : Configuration → ℝ,
      (∀ x, HasFDerivAt action (euler x) x) ∧
      FlowGaugeInvariant gaugeFlow action ∧
      action base = 0 := by
  refine ⟨radialAction base euler,
    radial_action_hasFDerivAt euler hDifferentiable hHelmholtz base,
    ?_, radial_action_at_base base euler⟩
  exact flow_gauge_invariant_of_euler_annihilates_generator
    gaugeFlow euler (radialAction base euler)
    (radial_action_hasFDerivAt euler hDifferentiable hHelmholtz base)
    hHorizontal

end P0EFTJanusNonlinearGaugeFlowNoether
end JanusFormal
