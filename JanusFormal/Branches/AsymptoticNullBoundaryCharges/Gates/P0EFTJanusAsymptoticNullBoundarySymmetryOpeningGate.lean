namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundarySymmetryOpeningGate

set_option autoImplicit false

structure AsymptoticNullBoundaryChargesSymmetryOpeningGate where
  infiniteDimensionalBoundarySymmetryRouteOpened : Prop
  bmsRouteAllowed : Prop
  newmanPenroseRouteAllowed : Prop
  covariantPhaseSpaceRouteAllowed : Prop
  finiteCP1EnergyBlockerTargeted : Prop
  alphaFitForbidden : Prop

def routeOpened (g : AsymptoticNullBoundaryChargesSymmetryOpeningGate) : Prop :=
  g.infiniteDimensionalBoundarySymmetryRouteOpened /\
  g.bmsRouteAllowed /\
  g.newmanPenroseRouteAllowed /\
  g.covariantPhaseSpaceRouteAllowed /\
  g.finiteCP1EnergyBlockerTargeted /\
  g.alphaFitForbidden

end P0EFTJanusAsymptoticNullBoundarySymmetryOpeningGate
end JanusFormal
