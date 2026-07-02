import JanusFormal.P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterNoRetuningReplayV2Gate

set_option autoImplicit false

structure MasterNoRetuningReplayV2Gate where
  observedPlanckWrapperHandshakeV2GatePassed : Prop
  normalizationFixedToASigma : Prop
  selectedRevisionFixed : Prop
  baselineSpectraExists : Prop
  candidateSpectraExists : Prop
  carrierThresholdPassed : Prop
  lambdaRetuningAllowed : Prop
  normalizationRetuningAllowed : Prop
  revisionRetuningAllowed : Prop
  newPhysicsChannelAllowed : Prop
  candidateReplayedWithoutRetuning : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def replayV2Ready (g : MasterNoRetuningReplayV2Gate) : Prop :=
  g.observedPlanckWrapperHandshakeV2GatePassed /\
  g.normalizationFixedToASigma /\
  g.selectedRevisionFixed /\
  g.baselineSpectraExists /\
  g.candidateSpectraExists /\
  g.carrierThresholdPassed /\
  Not g.lambdaRetuningAllowed /\
  Not g.normalizationRetuningAllowed /\
  Not g.revisionRetuningAllowed /\
  Not g.newPhysicsChannelAllowed /\
  g.candidateReplayedWithoutRetuning /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem replay_v2_without_retuning_still_blocks_promotion
    (g : MasterNoRetuningReplayV2Gate)
    (h : replayV2Ready g) :
    g.candidateReplayedWithoutRetuning /\
      Not g.candidatePromotionAllowed /\
      Not g.officialPlanckTrialAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hReplay, hNoPlanck, hNoPromotion, _, _, _⟩
  exact ⟨hReplay, hNoPromotion, hNoPlanck⟩

end P0EFTJanusZ4MasterNoRetuningReplayV2Gate
end JanusFormal
