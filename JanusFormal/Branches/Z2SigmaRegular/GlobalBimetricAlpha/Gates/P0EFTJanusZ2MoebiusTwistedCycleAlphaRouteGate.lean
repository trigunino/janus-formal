namespace JanusFormal
namespace P0EFTJanusZ2MoebiusTwistedCycleAlphaRouteGate

set_option autoImplicit false

structure MoebiusTwistedCycleAlphaRouteGate where
  twisted2DShadowReady : Prop
  z2OrientationCycleReady : Prop
  liftTo4DProjectiveTunnelReady : Prop
  thetaPeriodNonzero : Prop
  compactActionCycleReady : Prop

def alphaSelectorReady (g : MoebiusTwistedCycleAlphaRouteGate) : Prop :=
  g.twisted2DShadowReady /\
  g.z2OrientationCycleReady /\
  g.liftTo4DProjectiveTunnelReady /\
  g.thetaPeriodNonzero /\
  g.compactActionCycleReady

theorem zero_theta_blocks_moebius_alpha_selector
    (g : MoebiusTwistedCycleAlphaRouteGate)
    (hZero : Not g.thetaPeriodNonzero) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hZero h.2.2.2.1

theorem missing_compact_action_cycle_blocks_moebius_alpha_selector
    (g : MoebiusTwistedCycleAlphaRouteGate)
    (hMissing : Not g.compactActionCycleReady) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hMissing h.2.2.2.2

end P0EFTJanusZ2MoebiusTwistedCycleAlphaRouteGate
end JanusFormal
