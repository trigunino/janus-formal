namespace JanusFormal
namespace P0EFTJanusZ2SO3SignedSchwarzschildMetricDiagnosticGate

set_option autoImplicit false

structure SO3SignedSchwarzschildMetricDiagnosticGate where
  signedExteriorMetricBlocksDeclared : Prop
  sameSignAttractiveBlockDeclared : Prop
  oppositeSignRepulsiveBlockDeclared : Prop
  attractiveBlockDegenerateAtRs : Prop
  repulsiveBlockRegularAtRs : Prop
  thinShellKFormulaReadyAtRs : Prop
  regularThroatCollarRequired : Prop

def signedMetricDiagnosticReady
    (g : SO3SignedSchwarzschildMetricDiagnosticGate) : Prop :=
  g.signedExteriorMetricBlocksDeclared /\
  g.sameSignAttractiveBlockDeclared /\
  g.oppositeSignRepulsiveBlockDeclared /\
  g.attractiveBlockDegenerateAtRs /\
  g.repulsiveBlockRegularAtRs

theorem exterior_coordinate_degeneracy_blocks_thin_shell_K_at_Rs
    (g : SO3SignedSchwarzschildMetricDiagnosticGate)
    (_h : signedMetricDiagnosticReady g)
    (hNoK : Not g.thinShellKFormulaReadyAtRs) :
    Not g.thinShellKFormulaReadyAtRs := by
  exact hNoK

theorem regular_collar_is_required_if_thin_shell_K_not_ready
    (g : SO3SignedSchwarzschildMetricDiagnosticGate)
    (_hNoK : Not g.thinShellKFormulaReadyAtRs)
    (hReq : g.regularThroatCollarRequired) :
    g.regularThroatCollarRequired := by
  exact hReq

end P0EFTJanusZ2SO3SignedSchwarzschildMetricDiagnosticGate
end JanusFormal
