import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CompleteConventionHandshake

namespace JanusFormal
namespace P0EFTJanusZ4CompleteObservedPlanckDiagnosticGate

set_option autoImplicit false

structure CompleteObservedPlanckDiagnosticGate where
  calibrationPassed : Prop
  runObservedExecuted : Prop
  nonoverlapAccountingRequired : Prop
  cleanNonoverlapResult : Prop
  diagnosticTrialPassed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def diagnosticBlockedOrNonPromoting (g : CompleteObservedPlanckDiagnosticGate) : Prop :=
  g.calibrationPassed /\
  g.nonoverlapAccountingRequired /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem complete_observed_diagnostic_never_promotes_directly
    (g : CompleteObservedPlanckDiagnosticGate)
    (h : diagnosticBlockedOrNonPromoting g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  rcases h with âŸ¨_, _, hPromotion, _, hFullâŸ©
  exact âŸ¨hPromotion, hFullâŸ©

end P0EFTJanusZ4CompleteObservedPlanckDiagnosticGate
end JanusFormal
