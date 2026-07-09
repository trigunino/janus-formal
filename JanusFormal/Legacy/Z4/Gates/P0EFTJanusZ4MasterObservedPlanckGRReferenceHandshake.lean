import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshake

set_option autoImplicit false

structure MasterObservedPlanckGRReferenceHandshake where
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
  grReferenceHandshakePassed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def grReferenceHandshakeReady (g : MasterObservedPlanckGRReferenceHandshake) : Prop :=
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
  g.grReferenceHandshakePassed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem gr_reference_handshake_does_not_replay_candidate
    (g : MasterObservedPlanckGRReferenceHandshake)
    (h : grReferenceHandshakeReady g) :
    g.grReferenceHandshakePassed /\ Not g.candidateZ4ReplayPerformed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hReplay, _, _, _, hPassed, _, _⟩
  exact ⟨hPassed, hReplay⟩

end P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshake
end JanusFormal
