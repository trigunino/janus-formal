import JanusFormal.P0EFTJanusZ4MasterLikelihoodHandshakeGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterDiagnosticLikelihoodTrialGate

set_option autoImplicit false

structure MasterDiagnosticLikelihoodTrialGate where
  likelihoodHandshakePassed : Prop
  internalReferencePseudoLikelihood : Prop
  usesObservedPlanckData : Prop
  usesOfficialPlanckLikelihood : Prop
  nonoverlapAccounting : Prop
  diagnosticLikelihoodTrialPassed : Prop
  masterDerivedSignalPassedCarrierProjection : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def diagnosticTrialReady (g : MasterDiagnosticLikelihoodTrialGate) : Prop :=
  g.likelihoodHandshakePassed /\
  g.internalReferencePseudoLikelihood /\
  Not g.usesObservedPlanckData /\
  Not g.usesOfficialPlanckLikelihood /\
  g.nonoverlapAccounting /\
  g.diagnosticLikelihoodTrialPassed /\
  g.masterDerivedSignalPassedCarrierProjection /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem diagnostic_trial_makes_no_observational_claim
    (g : MasterDiagnosticLikelihoodTrialGate)
    (h : diagnosticTrialReady g) :
    g.diagnosticLikelihoodTrialPassed /\ Not g.observationalClaimAllowed := by
  rcases h with ⟨_, _, _, _, _, hTrial, _, _, _, hClaim, _, _⟩
  exact ⟨hTrial, hClaim⟩

end P0EFTJanusZ4MasterDiagnosticLikelihoodTrialGate
end JanusFormal
