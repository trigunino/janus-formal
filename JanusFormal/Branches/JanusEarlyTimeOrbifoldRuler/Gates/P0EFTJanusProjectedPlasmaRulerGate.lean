namespace JanusFormal
namespace P0EFTJanusProjectedPlasmaRulerGate

set_option autoImplicit false

structure ProjectedPlasmaRulerGate where
  projectedPhotonBaryonPlasmaDeclared : Prop
  nativeSoundSpeedDerived : Prop
  nativeDragRateDerived : Prop
  nativeDragRedshiftSolved : Prop
  nativePreDragHubbleDerived : Prop
  noLCDMSoundHorizonReuse : Prop
  routeClosed : Prop

def projectedPlasmaRouteBlocked (g : ProjectedPlasmaRulerGate) : Prop :=
  g.projectedPhotonBaryonPlasmaDeclared /\
  Not g.nativeSoundSpeedDerived /\
  Not g.nativeDragRateDerived /\
  Not g.nativeDragRedshiftSolved /\
  Not g.nativePreDragHubbleDerived /\
  g.noLCDMSoundHorizonReuse /\
  Not g.routeClosed

theorem plasma_route_needs_active_primitives
    (g : ProjectedPlasmaRulerGate)
    (h : projectedPlasmaRouteBlocked g) :
    Not g.routeClosed := by
  exact h.2.2.2.2.2.2

end P0EFTJanusProjectedPlasmaRulerGate
end JanusFormal
