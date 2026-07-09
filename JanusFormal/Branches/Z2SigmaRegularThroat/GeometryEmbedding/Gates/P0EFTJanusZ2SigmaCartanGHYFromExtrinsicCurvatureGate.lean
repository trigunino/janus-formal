namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYFromExtrinsicCurvatureGate

set_option autoImplicit false

structure CartanGHYFromExtrinsicCurvatureGate where
  cartanGHYFromKPlusMinusBuilderReady : Prop
  composesDeltaKJumpBuilder : Prop
  composesCartanGHYComponentBuilder : Prop
  requiresActiveKPlusMinusOfA : Prop
  requiresExplicitZ2Orientation : Prop
  requiresExplicitKappaRhoCrit0 : Prop
  usesPlanckLCDMInputs : Prop
  usesArchivedZ4Inputs : Prop
  cartanGHYValuesReady : Prop

def strictCartanGHYFromExtrinsicCurvatureReady
    (g : CartanGHYFromExtrinsicCurvatureGate) : Prop :=
  g.cartanGHYFromKPlusMinusBuilderReady /\
  g.composesDeltaKJumpBuilder /\
  g.composesCartanGHYComponentBuilder /\
  g.requiresActiveKPlusMinusOfA /\
  g.requiresExplicitZ2Orientation /\
  g.requiresExplicitKappaRhoCrit0 /\
  ¬ g.usesPlanckLCDMInputs /\
  ¬ g.usesArchivedZ4Inputs

theorem cartan_ghy_values_require_active_K_plus_minus
    (g : CartanGHYFromExtrinsicCurvatureGate)
    (hValues : g.cartanGHYValuesReady)
    (hImplies : g.cartanGHYValuesReady -> g.requiresActiveKPlusMinusOfA) :
    g.requiresActiveKPlusMinusOfA := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaCartanGHYFromExtrinsicCurvatureGate
end JanusFormal
