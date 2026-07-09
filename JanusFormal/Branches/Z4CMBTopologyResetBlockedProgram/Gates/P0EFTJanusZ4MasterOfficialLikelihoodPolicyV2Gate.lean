import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterDiagnosticLikelihoodTrialV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterOfficialLikelihoodPolicyV2Gate

set_option autoImplicit false

structure MasterOfficialLikelihoodPolicyV2Gate where
  diagnosticLikelihoodTrialV2Passed : Prop
  diagnosticTrialUsesObservedPlanckData : Prop
  diagnosticTrialUsesOfficialPlanckLikelihood : Prop
  officialLikelihoodPolicyDeclared : Prop
  observedPlanckWrapperDeclared : Prop
  grReferenceHandshakeOnSameWrapper : Prop
  masterV2NoRetuningReplay : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def officialPolicyV2Blocked (g : MasterOfficialLikelihoodPolicyV2Gate) : Prop :=
  g.diagnosticLikelihoodTrialV2Passed /\
  Not g.diagnosticTrialUsesObservedPlanckData /\
  Not g.diagnosticTrialUsesOfficialPlanckLikelihood /\
  g.officialLikelihoodPolicyDeclared /\
  Not g.observedPlanckWrapperDeclared /\
  Not g.grReferenceHandshakeOnSameWrapper /\
  Not g.masterV2NoRetuningReplay /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem policy_v2_blocks_official_planck_until_wrapper_handshake
    (g : MasterOfficialLikelihoodPolicyV2Gate)
    (h : officialPolicyV2Blocked g) :
    Not g.officialPlanckTrialAllowed /\ Not g.observationalClaimAllowed := by
  rcases h with âŸ¨_, _, _, _, _, _, _, hNoPlanck, _, hNoClaim, _, _âŸ©
  exact âŸ¨hNoPlanck, hNoClaimâŸ©

end P0EFTJanusZ4MasterOfficialLikelihoodPolicyV2Gate
end JanusFormal
