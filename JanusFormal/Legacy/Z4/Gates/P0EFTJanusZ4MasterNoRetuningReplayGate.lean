import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshake

namespace JanusFormal
namespace P0EFTJanusZ4MasterNoRetuningReplayGate

set_option autoImplicit false

structure MasterNoRetuningReplayGate where
  observedPlanckWrapperHandshakeGatePassed : Prop
  normalizationFixedToASigma : Prop
  baselineSpectraExists : Prop
  candidateSpectraExists : Prop
  carrierThresholdPassed : Prop
  lambdaRetuningAllowed : Prop
  normalizationRetuningAllowed : Prop
  newPhysicsChannelAllowed : Prop
  candidateReplayedWithoutRetuning : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def replayReady (g : MasterNoRetuningReplayGate) : Prop :=
  g.observedPlanckWrapperHandshakeGatePassed /\
  g.normalizationFixedToASigma /\
  g.baselineSpectraExists /\
  g.candidateSpectraExists /\
  g.carrierThresholdPassed /\
  Not g.lambdaRetuningAllowed /\
  Not g.normalizationRetuningAllowed /\
  Not g.newPhysicsChannelAllowed /\
  g.candidateReplayedWithoutRetuning /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem replay_without_retuning_still_blocks_promotion
    (g : MasterNoRetuningReplayGate)
    (h : replayReady g) :
    g.candidateReplayedWithoutRetuning /\ Not g.candidatePromotionAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hReplay, _, hPromotion, _, _, _⟩
  exact ⟨hReplay, hPromotion⟩

end P0EFTJanusZ4MasterNoRetuningReplayGate
end JanusFormal
