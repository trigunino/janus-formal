import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedNonOverlapAccountingGate

set_option autoImplicit false

structure MasterObservedNonOverlapAccountingGate where
  observedTrialExecuted : Prop
  nonoverlapAccountingPerformed : Prop
  cleanNonoverlapResult : Prop
  observedMasterBranchRejected : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def rejectedAccountingReady (g : MasterObservedNonOverlapAccountingGate) : Prop :=
  g.observedTrialExecuted /\
  g.nonoverlapAccountingPerformed /\
  Not g.cleanNonoverlapResult /\
  g.observedMasterBranchRejected /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

def pendingAccountingReady (g : MasterObservedNonOverlapAccountingGate) : Prop :=
  Not g.observedTrialExecuted /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem accounting_never_promotes_directly
    (g : MasterObservedNonOverlapAccountingGate)
    (h : rejectedAccountingReady g âˆ¨ pendingAccountingReady g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  cases h with
  | inl hRejected =>
      rcases hRejected with âŸ¨_, _, _, _, hPromotion, _, hFullâŸ©
      exact âŸ¨hPromotion, hFullâŸ©
  | inr hPending =>
      rcases hPending with âŸ¨_, hPromotion, _, hFullâŸ©
      exact âŸ¨hPromotion, hFullâŸ©

end P0EFTJanusZ4MasterObservedNonOverlapAccountingGate
end JanusFormal
