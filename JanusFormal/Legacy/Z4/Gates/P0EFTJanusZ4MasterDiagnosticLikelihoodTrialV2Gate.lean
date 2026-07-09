import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterLikelihoodHandshakeV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterDiagnosticLikelihoodTrialV2Gate

set_option autoImplicit false

structure MasterDiagnosticLikelihoodTrialV2Gate where
  likelihoodHandshakeV2Passed : Prop
  internalReferencePseudoLikelihoodV2 : Prop
  usesObservedPlanckData : Prop
  usesOfficialPlanckLikelihood : Prop
  likelihoodEvaluationAllowed : Prop
  nonoverlapAccounting : Prop
  overlappingSumForbidden : Prop
  diagnosticLikelihoodTrialV2Passed : Prop
  masterDerivedSignalPassedCarrierProjection : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def diagnosticTrialV2Ready (g : MasterDiagnosticLikelihoodTrialV2Gate) : Prop :=
  g.likelihoodHandshakeV2Passed /\
  g.internalReferencePseudoLikelihoodV2 /\
  Not g.usesObservedPlanckData /\
  Not g.usesOfficialPlanckLikelihood /\
  Not g.likelihoodEvaluationAllowed /\
  g.nonoverlapAccounting /\
  g.overlappingSumForbidden /\
  g.diagnosticLikelihoodTrialV2Passed /\
  g.masterDerivedSignalPassedCarrierProjection /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem diagnostic_trial_v2_makes_no_observational_claim
    (g : MasterDiagnosticLikelihoodTrialV2Gate)
    (h : diagnosticTrialV2Ready g) :
    g.diagnosticLikelihoodTrialV2Passed /\
      Not g.usesObservedPlanckData /\
      Not g.usesOfficialPlanckLikelihood /\
      Not g.observationalClaimAllowed := by
  rcases h with ⟨_, _, hNoObserved, hNoOfficial, _, _, _, hTrial, _, _, _, hNoClaim, _, _⟩
  exact ⟨hTrial, hNoObserved, hNoOfficial, hNoClaim⟩

end P0EFTJanusZ4MasterDiagnosticLikelihoodTrialV2Gate
end JanusFormal
