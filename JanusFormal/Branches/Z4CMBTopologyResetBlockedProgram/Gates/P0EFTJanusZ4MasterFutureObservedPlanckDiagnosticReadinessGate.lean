import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterLensingRemapPolicyGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterFutureObservedPlanckDiagnosticReadinessGate

set_option autoImplicit false

structure MasterFutureObservedPlanckDiagnosticReadinessGate where
  futureObservedPlanckDiagnosticAllowed : Prop
  unlensedLensedSplitAvailable : Prop
  provenanceManifestReady : Prop
  nonRetuningGuardPassed : Prop
  retuningAllowed : Prop
  candidatePromotionAllowed : Prop
  observedPlanckValidation : Prop
  fullPlanckValidation : Prop

def futureDiagnosticReady (g : MasterFutureObservedPlanckDiagnosticReadinessGate) : Prop :=
  g.futureObservedPlanckDiagnosticAllowed /\
  g.unlensedLensedSplitAvailable /\
  g.provenanceManifestReady /\
  g.nonRetuningGuardPassed /\
  Not g.retuningAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observedPlanckValidation /\
  Not g.fullPlanckValidation

theorem future_diagnostic_is_not_validation
    (g : MasterFutureObservedPlanckDiagnosticReadinessGate)
    (h : futureDiagnosticReady g) :
    g.futureObservedPlanckDiagnosticAllowed /\ Not g.observedPlanckValidation /\
    Not g.fullPlanckValidation := by
  rcases h with âŸ¨hFuture, _, _, _, _, _, hObserved, hFullâŸ©
  exact âŸ¨hFuture, hObserved, hFullâŸ©

end P0EFTJanusZ4MasterFutureObservedPlanckDiagnosticReadinessGate
end JanusFormal
