import JanusFormal.Branches.Z2SigmaRegular.TransportForce.Gates.P0EFTJanusZ2SigmaAbstractTensorTransportBianchiGate
import JanusFormal.Branches.Z2SigmaRegular.TransportForce.Gates.P0EFTJanusZ2SigmaTransportMapDerivationGate
import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaWeakFieldPoissonInteractionSignGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBridgeDeterminantFactorAuditGate

set_option autoImplicit false

structure BridgeDeterminantFactorAuditGate where
  abstractBianchiGateImported : Prop
  transportMapDerivationGateImported : Prop
  weakFieldPoissonSignGateImported : Prop
  bPlusDeclared : Prop
  bMinusDeclared : Prop
  bPlusBMinusReciprocal : Prop
  determinantFactorsKeptOutsideBridge : Prop
  stressTransportUsesBridgeOnly : Prop
  qCrossUsesSameBridgeOnly : Prop
  noQcrossDeterminantAbsorption : Prop
  plusRhsUsesBPlusKPlus : Prop
  minusRhsUsesBMinusKMinus : Prop
  bPlusNewtonianLimitOne : Prop
  bMinusNewtonianLimitOne : Prop
  weakFieldSignMatrixUnchanged : Prop
  feedsFormalBianchiLedger : Prop

def bridgeDeterminantFactorAuditReady
    (g : BridgeDeterminantFactorAuditGate) : Prop :=
  g.abstractBianchiGateImported /\
  g.transportMapDerivationGateImported /\
  g.weakFieldPoissonSignGateImported /\
  g.bPlusDeclared /\
  g.bMinusDeclared /\
  g.bPlusBMinusReciprocal /\
  g.determinantFactorsKeptOutsideBridge /\
  g.stressTransportUsesBridgeOnly /\
  g.qCrossUsesSameBridgeOnly /\
  g.noQcrossDeterminantAbsorption /\
  g.plusRhsUsesBPlusKPlus /\
  g.minusRhsUsesBMinusKMinus /\
  g.bPlusNewtonianLimitOne /\
  g.bMinusNewtonianLimitOne /\
  g.weakFieldSignMatrixUnchanged /\
  g.feedsFormalBianchiLedger

theorem determinant_audit_keeps_qcross_outside_volume_factor
    (g : BridgeDeterminantFactorAuditGate)
    (hReady : bridgeDeterminantFactorAuditReady g) :
    g.noQcrossDeterminantAbsorption /\ g.qCrossUsesSameBridgeOnly := by
  exact And.intro hReady.right.right.right.right.right.right.right.right.right.left
    hReady.right.right.right.right.right.right.right.right.left

theorem determinant_audit_newtonian_limit_preserves_sign_matrix
    (g : BridgeDeterminantFactorAuditGate)
    (hReady : bridgeDeterminantFactorAuditReady g) :
    g.bPlusNewtonianLimitOne /\
      g.bMinusNewtonianLimitOne /\
      g.weakFieldSignMatrixUnchanged := by
  exact And.intro hReady.right.right.right.right.right.right.right.right.right.right.right.right.left
    (And.intro hReady.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      hReady.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left)

theorem determinant_audit_feeds_bianchi_ledger
    (g : BridgeDeterminantFactorAuditGate)
    (hReady : bridgeDeterminantFactorAuditReady g) :
    g.determinantFactorsKeptOutsideBridge /\ g.feedsFormalBianchiLedger := by
  exact And.intro hReady.right.right.right.right.right.right.left
    hReady.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right

end P0EFTJanusZ2SigmaBridgeDeterminantFactorAuditGate
end JanusFormal
