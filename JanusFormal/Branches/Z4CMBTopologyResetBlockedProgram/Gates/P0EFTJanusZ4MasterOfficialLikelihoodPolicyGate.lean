import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterDiagnosticLikelihoodTrialGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterOfficialLikelihoodPolicyGate

set_option autoImplicit false

structure MasterOfficialLikelihoodPolicyGate where
  diagnosticLikelihoodTrialPassed : Prop
  diagnosticTrialUsesObservedPlanckData : Prop
  diagnosticTrialUsesOfficialPlanckLikelihood : Prop
  officialLikelihoodPolicyDeclared : Prop
  observedPlanckWrapperDeclared : Prop
  grReferenceHandshakeOnSameWrapper : Prop
  masterCandidateNoRetuningReplay : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def officialPolicyBlocked (g : MasterOfficialLikelihoodPolicyGate) : Prop :=
  g.diagnosticLikelihoodTrialPassed /\
  Not g.diagnosticTrialUsesObservedPlanckData /\
  Not g.diagnosticTrialUsesOfficialPlanckLikelihood /\
  g.officialLikelihoodPolicyDeclared /\
  Not g.observedPlanckWrapperDeclared /\
  Not g.grReferenceHandshakeOnSameWrapper /\
  Not g.masterCandidateNoRetuningReplay /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem policy_blocks_official_planck_until_wrapper_handshake
    (g : MasterOfficialLikelihoodPolicyGate)
    (h : officialPolicyBlocked g) :
    Not g.officialPlanckTrialAllowed /\ Not g.observationalClaimAllowed := by
  rcases h with âŸ¨_, _, _, _, _, _, _, hPlanck, _, hClaim, _, _âŸ©
  exact âŸ¨hPlanck, hClaimâŸ©

end P0EFTJanusZ4MasterOfficialLikelihoodPolicyGate
end JanusFormal
