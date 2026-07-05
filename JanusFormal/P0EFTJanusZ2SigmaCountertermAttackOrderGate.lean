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
  noCountertermChannelDropped : Prop
  noFitShortcut : Prop
  noLegacyZ4Import : Prop
  nearestChannelIdentified : Prop
  tetradChannelIsNearestNotReady : Prop
  activeEmbeddingReady : Prop
  rSigmaSolutionCertificateReady : Prop
  countertermAttackOrderReady : Prop

def countertermAttackOrderLedgerDeclared
    (g : CountertermAttackOrderGate) : Prop :=
  g.residualChannelFrontierImported /\
  g.tetradResidualChannelImported /\
  g.activeEmbeddingReadinessImported /\
  g.throatRadiusSolutionFrontierImported /\
  g.attackOrderIsDiagnosticOnly /\
  g.noCountertermChannelDropped /\
  g.noFitShortcut /\
  g.noLegacyZ4Import

def countertermAttackOrderGatePassed
    (g : CountertermAttackOrderGate) : Prop :=
  countertermAttackOrderLedgerDeclared g /\
  g.nearestChannelIdentified /\
  g.tetradChannelIsNearestNotReady /\
  g.activeEmbeddingReady /\
  g.rSigmaSolutionCertificateReady /\
  g.countertermAttackOrderReady

theorem attack_order_requires_rSigma_certificate
    (g : CountertermAttackOrderGate)
    (h : countertermAttackOrderGatePassed g) :
    g.rSigmaSolutionCertificateReady := by
  exact h.2.2.2.2.1

theorem missing_rSigma_certificate_blocks_attack_order
    (g : CountertermAttackOrderGate)
    (hMissing : Not g.rSigmaSolutionCertificateReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  exact hMissing (attack_order_requires_rSigma_certificate g hReady)

theorem diagnostic_nearest_tetrad_does_not_close_attack_order
    (g : CountertermAttackOrderGate)
    (hNotReady : Not g.countertermAttackOrderReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  exact hNotReady hReady.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermAttackOrderGate
end JanusFormal
