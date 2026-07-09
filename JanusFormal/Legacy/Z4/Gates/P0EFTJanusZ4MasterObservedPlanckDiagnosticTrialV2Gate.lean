import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterNoRetuningReplayV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialV2Gate

set_option autoImplicit false

structure MasterObservedPlanckDiagnosticTrialV2Gate where
  noRetuningReplayV2GatePassed : Prop
  runObservedRequested : Prop
  runObservedExecuted : Prop
  nonoverlapAccountingRequired : Prop
  diagnosticTrialAllowed : Prop
  diagnosticTrialPassed : Prop
  cleanNonoverlapResult : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def optInDiagnosticTrialV2Ready (g : MasterObservedPlanckDiagnosticTrialV2Gate) : Prop :=
  g.noRetuningReplayV2GatePassed /\
  Not g.runObservedRequested /\
  Not g.runObservedExecuted /\
  g.nonoverlapAccountingRequired /\
  g.diagnosticTrialAllowed /\
  g.diagnosticTrialPassed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

def executedDiagnosticTrialV2Ready (g : MasterObservedPlanckDiagnosticTrialV2Gate) : Prop :=
  g.noRetuningReplayV2GatePassed /\
  g.runObservedRequested /\
  g.runObservedExecuted /\
  g.nonoverlapAccountingRequired /\
  g.diagnosticTrialAllowed /\
  g.diagnosticTrialPassed /\
  g.cleanNonoverlapResult /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem diagnostic_trial_v2_never_promotes_directly
    (g : MasterObservedPlanckDiagnosticTrialV2Gate)
    (h : optInDiagnosticTrialV2Ready g \/ executedDiagnosticTrialV2Ready g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  cases h with
  | inl hOpt =>
      rcases hOpt with ⟨_, _, _, _, _, _, hNoPromotion, _, hNoFull⟩
      exact ⟨hNoPromotion, hNoFull⟩
  | inr hExec =>
      rcases hExec with ⟨_, _, _, _, _, _, _, hNoPromotion, _, hNoFull⟩
      exact ⟨hNoPromotion, hNoFull⟩

end P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialV2Gate
end JanusFormal
