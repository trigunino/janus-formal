import JanusFormal.P0EFTJanusZ4MasterLensingRemapPolicyGate

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
  rcases h with ⟨hFuture, _, _, _, _, _, hObserved, hFull⟩
  exact ⟨hFuture, hObserved, hFull⟩

end P0EFTJanusZ4MasterFutureObservedPlanckDiagnosticReadinessGate
end JanusFormal
