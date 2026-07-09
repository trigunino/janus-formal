namespace JanusFormal
namespace P0EFTJanusZ2SigmaTwoSectorConstantsChronologyAuditGate

set_option autoImplicit false

structure TwoSectorConstantsChronologyAuditGate where
  activeCoreZ2TunnelSigma : Prop
  commonChronologyParameterDeclared : Prop
  plusObserverTimeSeparated : Prop
  minusObserverTimeSeparated : Prop
  plusSectorConstantsDeclared : Prop
  minusSectorConstantsDeclared : Prop
  minusDistancesShorterClueRecorded : Prop
  minusLightSpeedHigherClueRecorded : Prop
  determinantLapseAuditRequired : Prop
  diagnosticOnly : Prop
  doesNotCloseRSigmaCertificate : Prop
  doesNotCloseBianchiTransport : Prop

def twoSectorConstantsChronologyAuditDeclared
    (g : TwoSectorConstantsChronologyAuditGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.commonChronologyParameterDeclared /\
  g.plusObserverTimeSeparated /\
  g.minusObserverTimeSeparated /\
  g.plusSectorConstantsDeclared /\
  g.minusSectorConstantsDeclared /\
  g.minusDistancesShorterClueRecorded /\
  g.minusLightSpeedHigherClueRecorded /\
  g.determinantLapseAuditRequired /\
  g.diagnosticOnly /\
  g.doesNotCloseRSigmaCertificate /\
  g.doesNotCloseBianchiTransport

theorem audit_is_diagnostic_only
    (g : TwoSectorConstantsChronologyAuditGate)
    (h : twoSectorConstantsChronologyAuditDeclared g) :
    g.diagnosticOnly /\
      g.doesNotCloseRSigmaCertificate /\
      g.doesNotCloseBianchiTransport := by
  exact And.intro h.right.right.right.right.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.right.right.right.right.left
      h.right.right.right.right.right.right.right.right.right.right.right)

end P0EFTJanusZ2SigmaTwoSectorConstantsChronologyAuditGate
end JanusFormal
