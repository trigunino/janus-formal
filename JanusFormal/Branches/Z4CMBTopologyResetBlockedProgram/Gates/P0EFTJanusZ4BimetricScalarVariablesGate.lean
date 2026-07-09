namespace JanusFormal
namespace P0EFTJanusZ4BimetricScalarVariablesGate

set_option autoImplicit false

structure BimetricScalarVariablesGate where
  visibleMetricPotentialsDeclared : Prop
  hiddenMetricPotentialsDeclared : Prop
  visibleFluidVariablesDeclared : Prop
  hiddenFluidVariablesDeclared : Prop
  projectionTermsDeclared : Prop
  mixingTermsDeclared : Prop
  anisotropicStressTermsDeclared : Prop
  torsionTermsDeclaredOrExplicitlyZero : Prop
  freeSlipParameter : Prop
  freeEtaRatio : Prop
  directClPatch : Prop
  rawToyLOS : Prop
  planckTrialAllowed : Prop
  variablesGatePassed : Prop

def variablesReady (g : BimetricScalarVariablesGate) : Prop :=
  g.visibleMetricPotentialsDeclared /\
  g.hiddenMetricPotentialsDeclared /\
  g.visibleFluidVariablesDeclared /\
  g.hiddenFluidVariablesDeclared /\
  g.projectionTermsDeclared /\
  g.mixingTermsDeclared /\
  g.anisotropicStressTermsDeclared /\
  g.torsionTermsDeclaredOrExplicitlyZero /\
  Not g.freeSlipParameter /\
  Not g.freeEtaRatio /\
  Not g.directClPatch /\
  Not g.rawToyLOS /\
  Not g.planckTrialAllowed

theorem variables_gate_passes_when_declarations_are_explicit
    (g : BimetricScalarVariablesGate)
    (hPolicy : variablesReady g -> g.variablesGatePassed)
    (h : variablesReady g) :
    g.variablesGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4BimetricScalarVariablesGate
end JanusFormal
