import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterOfficialLikelihoodPolicyGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeGate

set_option autoImplicit false

structure MasterObservedPlanckWrapperHandshakeGate where
  officialLikelihoodPolicyDeclared : Prop
  observedPlanckWrapperAvailable : Prop
  mockWrappersAllowed : Prop
  fallbackToInternalPseudoLikelihoodAllowed : Prop
  grReferenceHandshakeReportPresent : Prop
  grReferenceHandshakeOnSameWrapperPassed : Prop
  masterCandidateNoRetuningReplay : Prop
  observedPlanckWrapperHandshakeGatePassed : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def wrapperHandshakeBlocked (g : MasterObservedPlanckWrapperHandshakeGate) : Prop :=
  g.officialLikelihoodPolicyDeclared /\
  Not g.mockWrappersAllowed /\
  Not g.fallbackToInternalPseudoLikelihoodAllowed /\
  Not g.grReferenceHandshakeOnSameWrapperPassed /\
  Not g.masterCandidateNoRetuningReplay /\
  Not g.observedPlanckWrapperHandshakeGatePassed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem no_gr_handshake_blocks_observed_planck
    (g : MasterObservedPlanckWrapperHandshakeGate)
    (h : wrapperHandshakeBlocked g) :
    Not g.officialPlanckTrialAllowed /\ Not g.observationalClaimAllowed := by
  rcases h with âŸ¨_, _, _, _, _, _, hPlanck, _, hClaim, _, _âŸ©
  exact âŸ¨hPlanck, hClaimâŸ©

end P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeGate
end JanusFormal
