import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterNoRetuningReplayGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialGate

set_option autoImplicit false

structure MasterObservedPlanckDiagnosticTrialGate where
  noRetuningReplayGatePassed : Prop
  runObservedRequested : Prop
  runObservedExecuted : Prop
  nonoverlapAccountingRequired : Prop
  diagnosticTrialAllowed : Prop
  diagnosticTrialPassed : Prop
  cleanNonoverlapResult : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def optInDiagnosticTrialReady (g : MasterObservedPlanckDiagnosticTrialGate) : Prop :=
  g.noRetuningReplayGatePassed /\
  Not g.runObservedRequested /\
  Not g.runObservedExecuted /\
  g.nonoverlapAccountingRequired /\
  g.diagnosticTrialAllowed /\
  g.diagnosticTrialPassed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

def executedDiagnosticTrialReady (g : MasterObservedPlanckDiagnosticTrialGate) : Prop :=
  g.noRetuningReplayGatePassed /\
  g.runObservedRequested /\
  g.runObservedExecuted /\
  g.nonoverlapAccountingRequired /\
  g.diagnosticTrialAllowed /\
  g.diagnosticTrialPassed /\
  g.cleanNonoverlapResult /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem diagnostic_trial_never_promotes_directly
    (g : MasterObservedPlanckDiagnosticTrialGate)
    (h : optInDiagnosticTrialReady g ∨ executedDiagnosticTrialReady g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  cases h with
  | inl hOpt =>
      rcases hOpt with ⟨_, _, _, _, _, _, hPromotion, _, hFull⟩
      exact ⟨hPromotion, hFull⟩
  | inr hExec =>
      rcases hExec with ⟨_, _, _, _, _, _, _, hPromotion, _, hFull⟩
      exact ⟨hPromotion, hFull⟩

end P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialGate
end JanusFormal
