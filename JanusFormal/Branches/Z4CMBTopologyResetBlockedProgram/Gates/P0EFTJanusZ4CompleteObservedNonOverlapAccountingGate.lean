import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CompleteObservedPlanckDiagnosticGate

namespace JanusFormal
namespace P0EFTJanusZ4CompleteObservedNonOverlapAccountingGate

set_option autoImplicit false

structure CompleteObservedNonOverlapAccountingGate where
  observedTrialExecuted : Prop
  nonoverlapAccountingPerformed : Prop
  legacyOverlappingTotalDiagnosticOnly : Prop
  cleanNonoverlapResult : Prop
  observedCompleteSolverBranchRejected : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def accountingReady (g : CompleteObservedNonOverlapAccountingGate) : Prop :=
  g.legacyOverlappingTotalDiagnosticOnly /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem nonoverlap_accounting_never_promotes_directly
    (g : CompleteObservedNonOverlapAccountingGate)
    (h : accountingReady g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  rcases h with âŸ¨_, hPromotion, _, hFullâŸ©
  exact âŸ¨hPromotion, hFullâŸ©

end P0EFTJanusZ4CompleteObservedNonOverlapAccountingGate
end JanusFormal
