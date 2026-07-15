import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeOrbitDescent

namespace JanusFormal
namespace P0EFTJanusGaugeOrbitInvariantEquiv

set_option autoImplicit false

open P0EFTJanusNonlinearGaugeFlowNoether
open P0EFTJanusGaugeOrbitDescent

/-- Functions on configurations that are constant along a complete gauge flow. -/
def FlowInvariantFunction
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (Target : Type*) :=
  { function : Configuration → Target //
    ∀ x t, function (gaugeFlow.flow t x) = function x }

/-- Pullback of a function on gauge orbits to configuration space. -/
def pullbackOrbitFunction
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (quotientFunction : GaugeOrbit gaugeFlow → Target) :
    Configuration → Target :=
  fun x ↦ quotientFunction (orbitClass gaugeFlow x)

theorem pullbackOrbitFunction_invariant
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (quotientFunction : GaugeOrbit gaugeFlow → Target) :
    ∀ x t,
      pullbackOrbitFunction gaugeFlow quotientFunction (gaugeFlow.flow t x) =
        pullbackOrbitFunction gaugeFlow quotientFunction x := by
  intro x t
  apply congrArg quotientFunction
  exact (Quotient.sound
    (show OrbitRel gaugeFlow x (gaugeFlow.flow t x) from ⟨t, rfl⟩)).symm

/-- Descent of an invariant function to the set-theoretic orbit quotient. -/
def descendInvariantFunction
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (invariantFunction : FlowInvariantFunction gaugeFlow Target) :
    GaugeOrbit gaugeFlow → Target :=
  Quotient.lift invariantFunction.1 (by
    intro x y hxy
    rcases hxy with ⟨t, rfl⟩
    exact (invariantFunction.2 x t).symm)

@[simp]
theorem descendInvariantFunction_orbitClass
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (invariantFunction : FlowInvariantFunction gaugeFlow Target)
    (x : Configuration) :
    descendInvariantFunction gaugeFlow invariantFunction
        (orbitClass gaugeFlow x) =
      invariantFunction.1 x :=
  rfl

/-- Functions on the set-theoretic orbit quotient are exactly the functions
on configuration space that are constant along every gauge orbit. -/
def orbitFunctionsEquivFlowInvariantFunctions
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration) :
    (GaugeOrbit gaugeFlow → Target) ≃
      FlowInvariantFunction gaugeFlow Target where
  toFun quotientFunction :=
    ⟨pullbackOrbitFunction gaugeFlow quotientFunction,
      pullbackOrbitFunction_invariant gaugeFlow quotientFunction⟩
  invFun invariantFunction :=
    descendInvariantFunction gaugeFlow invariantFunction
  left_inv quotientFunction := by
    funext orbit
    induction orbit using Quotient.inductionOn with
    | _ x => rfl
  right_inv invariantFunction := by
    apply Subtype.ext
    funext x
    rfl

@[simp]
theorem orbitFunctionsEquiv_apply
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (quotientFunction : GaugeOrbit gaugeFlow → Target)
    (x : Configuration) :
    (orbitFunctionsEquivFlowInvariantFunctions gaugeFlow quotientFunction).1 x =
      quotientFunction (orbitClass gaugeFlow x) :=
  rfl

@[simp]
theorem orbitFunctionsEquiv_symm_apply_orbitClass
    {Configuration Target : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration)
    (invariantFunction : FlowInvariantFunction gaugeFlow Target)
    (x : Configuration) :
    (orbitFunctionsEquivFlowInvariantFunctions gaugeFlow).symm
        invariantFunction (orbitClass gaugeFlow x) =
      invariantFunction.1 x :=
  rfl

/-- Real-valued specialization: quotient actions are equivalent to genuinely
flow-invariant actions on configuration space. -/
def orbitActionsEquivFlowGaugeInvariant
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (gaugeFlow : CompleteGaugeFlow Configuration) :
    (GaugeOrbit gaugeFlow → ℝ) ≃
      { action : Configuration → ℝ // FlowGaugeInvariant gaugeFlow action } :=
  orbitFunctionsEquivFlowInvariantFunctions gaugeFlow

end P0EFTJanusGaugeOrbitInvariantEquiv
end JanusFormal
