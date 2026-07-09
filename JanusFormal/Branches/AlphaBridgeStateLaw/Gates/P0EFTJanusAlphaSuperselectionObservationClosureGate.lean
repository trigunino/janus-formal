namespace JanusFormal
namespace P0EFTJanusAlphaSuperselectionObservationClosureGate

set_option autoImplicit false

structure AlphaObservationClosureGate where
  snBaoRunnerExecuted : Prop
  q0BoundarySelected : Prop
  interiorJanusSectorSelected : Prop
  baoRejectsCurrentProxy : Prop
  noFitClaimForbidden : Prop

def currentProxyClosedNegative (g : AlphaObservationClosureGate) : Prop :=
  g.snBaoRunnerExecuted /\
  g.q0BoundarySelected /\
  Not g.interiorJanusSectorSelected /\
  g.baoRejectsCurrentProxy /\
  g.noFitClaimForbidden

theorem current_proxy_does_not_select_interior_janus_sector
    (g : AlphaObservationClosureGate)
    (h : currentProxyClosedNegative g) :
    Not g.interiorJanusSectorSelected := by
  exact h.right.right.left

end P0EFTJanusAlphaSuperselectionObservationClosureGate
end JanusFormal
