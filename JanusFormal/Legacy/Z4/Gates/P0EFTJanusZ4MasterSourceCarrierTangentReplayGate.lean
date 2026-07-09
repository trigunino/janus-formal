import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterConstraintClosureAuditGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterSourceCarrierTangentReplayGate

set_option autoImplicit false

structure MasterSourceCarrierTangentReplayGate where
  masterConstraintClosureAuditPassed : Prop
  sourceLevelPayloadReplayed : Prop
  selectedMasterAnsatzReported : Prop
  allChannelsDerivedFromSameUZ4 : Prop
  carrierProjectionReported : Prop
  dominantTangentDirectionReported : Prop
  thresholdDecisionReported : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def replayReady (g : MasterSourceCarrierTangentReplayGate) : Prop :=
  g.masterConstraintClosureAuditPassed /\
  g.sourceLevelPayloadReplayed /\
  g.selectedMasterAnsatzReported /\
  g.allChannelsDerivedFromSameUZ4 /\
  g.carrierProjectionReported /\
  g.dominantTangentDirectionReported /\
  g.thresholdDecisionReported /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem master_source_carrier_replay_precedes_observation
    (g : MasterSourceCarrierTangentReplayGate)
    (hPolicy : replayReady g -> g.gatePassed)
    (h : replayReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterSourceCarrierTangentReplayGate
end JanusFormal
