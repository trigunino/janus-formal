import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonlinearGaugeFlowNoether

namespace JanusFormal
namespace P0EFTJanusGaugeOrbitDescent

set_option autoImplicit false

open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusNonlinearGaugeFlowNoether

/-- Two configurations lie on the same orbit of a complete gauge flow. -/
def OrbitRel
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (x y : Configuration) : Prop :=
  ∃ t : ℝ, y = gaugeFlow.flow t x

theorem orbitRel_refl
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (x : Configuration) :
    OrbitRel gaugeFlow x x := by
  exact ⟨0, (gaugeFlow.flow_zero x).symm⟩

theorem orbitRel_symm
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    {x y : Configuration}
    (hxy : OrbitRel gaugeFlow x y) :
    OrbitRel gaugeFlow y x := by
  rcases hxy with ⟨t, rfl⟩
  refine ⟨-t, ?_⟩
  calc
    x = gaugeFlow.flow 0 x := (gaugeFlow.flow_zero x).symm
    _ = gaugeFlow.flow ((-t) + t) x := by rw [neg_add_cancel]
    _ = gaugeFlow.flow (-t) (gaugeFlow.flow t x) :=
      gaugeFlow.flow_add (-t) t x

theorem orbitRel_trans
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    {x y z : Configuration}
    (hxy : OrbitRel gaugeFlow x y)
    (hyz : OrbitRel gaugeFlow y z) :
    OrbitRel gaugeFlow x z := by
  rcases hxy with ⟨t, rfl⟩
  rcases hyz with ⟨s, rfl⟩
  exact ⟨s + t, (gaugeFlow.flow_add s t x).symm⟩

/-- The setoid of full orbits of a complete gauge flow. -/
def orbitSetoid
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration) : Setoid Configuration where
  r := OrbitRel gaugeFlow
  iseqv := ⟨orbitRel_refl gaugeFlow, orbitRel_symm gaugeFlow,
    orbitRel_trans gaugeFlow⟩

/-- Configuration space modulo the supplied complete gauge flow. -/
def GaugeOrbit
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration) :=
  Quotient (orbitSetoid gaugeFlow)

/-- Canonical projection to gauge orbits. -/
def orbitClass
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (x : Configuration) : GaugeOrbit gaugeFlow :=
  Quotient.mk (orbitSetoid gaugeFlow) x

/-- A flow-invariant action evaluated on gauge-orbit classes. -/
def orbitAction
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (action : Configuration → ℝ)
    (hInvariant : FlowGaugeInvariant gaugeFlow action) :
    GaugeOrbit gaugeFlow → ℝ :=
  Quotient.lift action (by
    intro x y hxy
    rcases hxy with ⟨t, rfl⟩
    exact (hInvariant x t).symm)

@[simp]
theorem orbitAction_orbitClass
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (action : Configuration → ℝ)
    (hInvariant : FlowGaugeInvariant gaugeFlow action)
    (x : Configuration) :
    orbitAction gaugeFlow action hInvariant (orbitClass gaugeFlow x) = action x :=
  rfl

/-- Every invariant action factors uniquely through the gauge-orbit quotient. -/
theorem flow_gauge_invariant_unique_orbit_factor
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (action : Configuration → ℝ)
    (hInvariant : FlowGaugeInvariant gaugeFlow action) :
    ∃! quotientAction : GaugeOrbit gaugeFlow → ℝ,
      ∀ x, quotientAction (orbitClass gaugeFlow x) = action x := by
  refine ⟨orbitAction gaugeFlow action hInvariant, ?_, ?_⟩
  · exact orbitAction_orbitClass gaugeFlow action hInvariant
  · intro other hOther
    funext orbit
    induction orbit using Quotient.inductionOn with
    | _ x =>
        change other (orbitClass gaugeFlow x) =
          orbitAction gaugeFlow action hInvariant (orbitClass gaugeFlow x)
        rw [hOther x]
        rfl

/-- The radial action reconstructed from an integrable horizontal Euler
one-form descends uniquely to the quotient by the complete gauge flow. -/
theorem radial_reconstruction_unique_orbit_factor
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (hDifferentiable : Differentiable ℝ euler)
    (hHelmholtz : ∀ x, HelmholtzJacobianAt euler x)
    (hHorizontal : EulerAnnihilatesGenerator gaugeFlow euler)
    (base : Configuration) :
    ∃! quotientAction : GaugeOrbit gaugeFlow → ℝ,
      ∀ x, quotientAction (orbitClass gaugeFlow x) = radialAction base euler x := by
  apply flow_gauge_invariant_unique_orbit_factor
  exact flow_gauge_invariant_of_euler_annihilates_generator
    gaugeFlow euler (radialAction base euler)
    (radial_action_hasFDerivAt euler hDifferentiable hHelmholtz base)
    hHorizontal

end P0EFTJanusGaugeOrbitDescent
end JanusFormal
