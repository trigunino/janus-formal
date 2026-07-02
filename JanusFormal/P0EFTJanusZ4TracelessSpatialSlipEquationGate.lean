namespace JanusFormal
namespace P0EFTJanusZ4TracelessSpatialSlipEquationGate

set_option autoImplicit false

structure TracelessSpatialSlipEquationGate where
  linearizedTracelessSpatialEquationDeclared : Prop
  slipSourceDerivedFromFieldEquations : Prop
  visibleMetricPotentialsDeclared : Prop
  hiddenMetricPotentialsDeclared : Prop
  projectionTermsDeclared : Prop
  anisotropicStressTermsDeclared : Prop
  torsionTermsDeclaredOrExplicitlyZero : Prop
  grLimitSlipZero : Prop
  bianchiConsistencyChecked : Prop
  sourceLevelRegenerationRequired : Prop
  freeEtaRatio : Prop
  freeSlipAmplitude : Prop
  directClPatch : Prop
  rawToyLOS : Prop
  valueSlipTransportClosed : Prop
  planckTrialAllowed : Prop
  slipEquationGatePassed : Prop

def slipEquationReady (g : TracelessSpatialSlipEquationGate) : Prop :=
  g.linearizedTracelessSpatialEquationDeclared /\
  g.slipSourceDerivedFromFieldEquations /\
  g.visibleMetricPotentialsDeclared /\
  g.hiddenMetricPotentialsDeclared /\
  g.projectionTermsDeclared /\
  g.anisotropicStressTermsDeclared /\
  g.torsionTermsDeclaredOrExplicitlyZero /\
  g.grLimitSlipZero /\
  g.bianchiConsistencyChecked /\
  g.sourceLevelRegenerationRequired /\
  Not g.freeEtaRatio /\
  Not g.freeSlipAmplitude /\
  Not g.directClPatch /\
  Not g.rawToyLOS /\
  Not g.valueSlipTransportClosed /\
  Not g.planckTrialAllowed

theorem tracefree_spatial_rows_supply_slip_equation_only
    (g : TracelessSpatialSlipEquationGate)
    (hPolicy : slipEquationReady g -> g.slipEquationGatePassed)
    (h : slipEquationReady g) :
    g.slipEquationGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TracelessSpatialSlipEquationGate
end JanusFormal
