import JanusFormal.P0EFTJanusZ4MasterOfficialLikelihoodPolicyV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshakeV2

set_option autoImplicit false

structure MasterObservedPlanckGRReferenceHandshakeV2 where
  allObservedWrappersAvailable : Prop
  clVsDlConventionChecked : Prop
  unitsChecked : Prop
  teSignChecked : Prop
  ellIndexingChecked : Prop
  nuisanceVectorChecked : Prop
  foregroundHandlingChecked : Prop
  grReferenceSanityChecked : Prop
  candidateZ4ReplayPerformed : Prop
  lambdaRetuningAllowed : Prop
  officialPlanckTrialAllowed : Prop
  observationalClaimAllowed : Prop
  grReferenceHandshakeV2Passed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def grHandshakeV2Ready (g : MasterObservedPlanckGRReferenceHandshakeV2) : Prop :=
  g.allObservedWrappersAvailable /\
  g.clVsDlConventionChecked /\
  g.unitsChecked /\
  g.teSignChecked /\
  g.ellIndexingChecked /\
  g.nuisanceVectorChecked /\
  g.foregroundHandlingChecked /\
  g.grReferenceSanityChecked /\
  Not g.candidateZ4ReplayPerformed /\
  Not g.lambdaRetuningAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.observationalClaimAllowed /\
  g.grReferenceHandshakeV2Passed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem gr_reference_v2_is_handshake_not_candidate_replay
    (g : MasterObservedPlanckGRReferenceHandshakeV2)
    (h : grHandshakeV2Ready g) :
    g.grReferenceHandshakeV2Passed /\ Not g.candidateZ4ReplayPerformed /\ Not g.officialPlanckTrialAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hNoReplay, _, hNoPlanck, _, hPassed, _, _⟩
  exact ⟨hPassed, hNoReplay, hNoPlanck⟩

end P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshakeV2
end JanusFormal
