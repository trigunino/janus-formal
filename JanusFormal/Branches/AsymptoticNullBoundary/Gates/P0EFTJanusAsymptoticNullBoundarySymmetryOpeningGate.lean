namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundarySymmetryOpeningGate

set_option autoImplicit false

structure AsymptoticNullBoundarySymmetryOpeningGate where
  infiniteDimensionalBoundarySymmetryRouteOpened : Prop
  bmsRouteAllowed : Prop
  newmanPenroseRouteAllowed : Prop
  covariantPhaseSpaceRouteAllowed : Prop
  finiteCP1EnergyBlockerTargeted : Prop
  alphaFitForbidden : Prop

def routeOpened (g : AsymptoticNullBoundarySymmetryOpeningGate) : Prop :=
  g.infiniteDimensionalBoundarySymmetryRouteOpened /\
  g.bmsRouteAllowed /\
  g.newmanPenroseRouteAllowed /\
  g.covariantPhaseSpaceRouteAllowed /\
  g.finiteCP1EnergyBlockerTargeted /\
  g.alphaFitForbidden

end P0EFTJanusAsymptoticNullBoundarySymmetryOpeningGate
end JanusFormal
