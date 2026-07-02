import JanusFormal.P0EFTJanusZ4MasterToObservableMapGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterCarrierTangentProjectionGate

set_option autoImplicit false

structure MasterCarrierTangentProjectionGate where
  masterToObservableMapGatePassed : Prop
  allChannelsDerivedFromSameUZ4 : Prop
  carrierProjectionReported : Prop
  dominantTangentDirectionReported : Prop
  successThresholdReported : Prop
  strongThresholdReported : Prop
  archiveDecisionReported : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def projectionGateReady (g : MasterCarrierTangentProjectionGate) : Prop :=
  g.masterToObservableMapGatePassed /\
  g.allChannelsDerivedFromSameUZ4 /\
  g.carrierProjectionReported /\
  g.dominantTangentDirectionReported /\
  g.successThresholdReported /\
  g.strongThresholdReported /\
  g.archiveDecisionReported /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem master_carrier_projection_precedes_observation
    (g : MasterCarrierTangentProjectionGate)
    (hPolicy : projectionGateReady g -> g.gatePassed)
    (h : projectionGateReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterCarrierTangentProjectionGate
end JanusFormal
