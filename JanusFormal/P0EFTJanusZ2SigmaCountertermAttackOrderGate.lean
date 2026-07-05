import JanusFormal.P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
import JanusFormal.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate
import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermAttackOrderGate

set_option autoImplicit false

structure CountertermAttackOrderGate where
  residualChannelFrontierImported : Prop
  tetradResidualChannelImported : Prop
  activeEmbeddingReadinessImported : Prop
  throatRadiusSolutionFrontierImported : Prop
  attackOrderIsDiagnosticOnly : Prop
  circularRadiusCountertermDependencyChecked : Prop
  symbolicLocalCountertermRouteDeclared : Prop
  noCountertermChannelDropped : Prop
  noFitShortcut : Prop
  noLegacyZ4Import : Prop
  nearestChannelIdentified : Prop
  tetradChannelIsNearestNotReady : Prop
  radiusCountertermCircularDependencyDetected : Prop
  activeEmbeddingReady : Prop
  rSigmaSolutionCertificateReady : Prop
  symbolicLocalCountertermRouteReady : Prop
  countertermAttackOrderReady : Prop

def countertermAttackOrderLedgerDeclared
    (g : CountertermAttackOrderGate) : Prop :=
  g.residualChannelFrontierImported /\
  g.tetradResidualChannelImported /\
  g.activeEmbeddingReadinessImported /\
  g.throatRadiusSolutionFrontierImported /\
  g.attackOrderIsDiagnosticOnly /\
  g.circularRadiusCountertermDependencyChecked /\
  g.symbolicLocalCountertermRouteDeclared /\
  g.noCountertermChannelDropped /\
  g.noFitShortcut /\
  g.noLegacyZ4Import

def countertermAttackOrderGatePassed
    (g : CountertermAttackOrderGate) : Prop :=
  countertermAttackOrderLedgerDeclared g /\
  g.nearestChannelIdentified /\
  g.tetradChannelIsNearestNotReady /\
  g.radiusCountertermCircularDependencyDetected /\
  g.symbolicLocalCountertermRouteReady /\
  g.activeEmbeddingReady /\
  g.rSigmaSolutionCertificateReady /\
  g.countertermAttackOrderReady

theorem attack_order_requires_symbolic_local_counterterm_route
    (g : CountertermAttackOrderGate)
    (h : countertermAttackOrderGatePassed g) :
    g.symbolicLocalCountertermRouteReady := by
  rcases h with ⟨_, _, _, _, hSymbolic, _, _, _⟩
  exact hSymbolic

theorem missing_symbolic_local_counterterm_route_blocks_attack_order
    (g : CountertermAttackOrderGate)
    (hMissing : Not g.symbolicLocalCountertermRouteReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  exact hMissing (attack_order_requires_symbolic_local_counterterm_route g hReady)

theorem diagnostic_nearest_tetrad_does_not_close_attack_order
    (g : CountertermAttackOrderGate)
    (hNotReady : Not g.countertermAttackOrderReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  rcases hReady with ⟨_, _, _, _, _, _, _, hCounterterm⟩
  exact hNotReady hCounterterm

end P0EFTJanusZ2SigmaCountertermAttackOrderGate
end JanusFormal
