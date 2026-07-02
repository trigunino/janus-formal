import JanusFormal.P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedNonOverlapAccountingV2Gate

set_option autoImplicit false

structure MasterObservedNonOverlapAccountingV2Gate where
  observedTrialExecuted : Prop
  nonoverlapAccountingPerformed : Prop
  cleanNonoverlapResult : Prop
  observedMasterV2BranchRejected : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def rejectedAccountingV2Ready (g : MasterObservedNonOverlapAccountingV2Gate) : Prop :=
  g.observedTrialExecuted /\
  g.nonoverlapAccountingPerformed /\
  Not g.cleanNonoverlapResult /\
  g.observedMasterV2BranchRejected /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

def cleanAccountingV2Ready (g : MasterObservedNonOverlapAccountingV2Gate) : Prop :=
  g.observedTrialExecuted /\
  g.nonoverlapAccountingPerformed /\
  g.cleanNonoverlapResult /\
  Not g.observedMasterV2BranchRejected /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

def pendingAccountingV2Ready (g : MasterObservedNonOverlapAccountingV2Gate) : Prop :=
  Not g.observedTrialExecuted /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem accounting_v2_never_promotes_directly
    (g : MasterObservedNonOverlapAccountingV2Gate)
    (h : rejectedAccountingV2Ready g \/ cleanAccountingV2Ready g \/ pendingAccountingV2Ready g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  cases h with
  | inl hRejected =>
      rcases hRejected with ⟨_, _, _, _, hPromotion, _, hFull⟩
      exact ⟨hPromotion, hFull⟩
  | inr hRest =>
      cases hRest with
      | inl hClean =>
          rcases hClean with ⟨_, _, _, _, hPromotion, _, hFull⟩
          exact ⟨hPromotion, hFull⟩
      | inr hPending =>
          rcases hPending with ⟨_, hPromotion, _, hFull⟩
          exact ⟨hPromotion, hFull⟩

end P0EFTJanusZ4MasterObservedNonOverlapAccountingV2Gate
end JanusFormal
