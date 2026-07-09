import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterUnlensedLensedSplitGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterLensingRemapPolicyGate

set_option autoImplicit false

structure MasterLensingRemapPolicyGate where
  unlensedLensedSplitAvailable : Prop
  lensedRemapGenerated : Prop
  policyAllowsFutureObservedDiagnostic : Prop
  observedLikelihoodAllowedNow : Prop
  planckRetryAllowedNow : Prop
  candidatePromotionAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def policyReady (g : MasterLensingRemapPolicyGate) : Prop :=
  g.unlensedLensedSplitAvailable /\
  g.lensedRemapGenerated /\
  g.policyAllowsFutureObservedDiagnostic /\
  Not g.observedLikelihoodAllowedNow /\
  Not g.planckRetryAllowedNow /\
  Not g.candidatePromotionAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem policy_allows_future_diagnostic_not_current_validation
    (g : MasterLensingRemapPolicyGate)
    (h : policyReady g) :
    g.policyAllowsFutureObservedDiagnostic /\ Not g.fullPlanckValidation := by
  rcases h with ⟨_, _, hFuture, _, _, _, _, hFull⟩
  exact ⟨hFuture, hFull⟩

end P0EFTJanusZ4MasterLensingRemapPolicyGate
end JanusFormal
