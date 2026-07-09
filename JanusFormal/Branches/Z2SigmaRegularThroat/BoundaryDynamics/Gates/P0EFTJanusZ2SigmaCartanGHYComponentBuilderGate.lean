namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYComponentBuilderGate

set_option autoImplicit false

structure CartanGHYComponentBuilderGate where
  deltaKToComponentBuilderReady : Prop
  rhoCartanGHYOverRhoCrit0BuilderReady : Prop
  pCartanGHYOverRhoCrit0BuilderReady : Prop
  requiresActiveDeltaKsOfA : Prop
  requiresActiveDeltaKtauOfA : Prop
  requiresExplicitZ2OrientationSign : Prop
  requiresExplicitKappaRhoCrit0 : Prop
  cartanGHYComponentValuesReady : Prop

def strictCartanGHYComponentBuilderReady
    (g : CartanGHYComponentBuilderGate) : Prop :=
  g.deltaKToComponentBuilderReady /\
  g.rhoCartanGHYOverRhoCrit0BuilderReady /\
  g.pCartanGHYOverRhoCrit0BuilderReady /\
  g.requiresActiveDeltaKsOfA /\
  g.requiresActiveDeltaKtauOfA /\
  g.requiresExplicitZ2OrientationSign /\
  g.requiresExplicitKappaRhoCrit0

theorem component_values_require_deltaK_inputs
    (g : CartanGHYComponentBuilderGate)
    (hValues : g.cartanGHYComponentValuesReady)
    (hImplies :
      g.cartanGHYComponentValuesReady ->
        g.requiresActiveDeltaKsOfA /\ g.requiresActiveDeltaKtauOfA) :
    g.requiresActiveDeltaKsOfA /\ g.requiresActiveDeltaKtauOfA := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaCartanGHYComponentBuilderGate
end JanusFormal
