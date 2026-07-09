import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterRevisedSourceLevelRegenerationGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterRevisedCarrierTangentProjectionGate

set_option autoImplicit false

structure MasterRevisedCarrierTangentProjectionGate where
  sourceLevelV2Passed : Prop
  carrierThresholdPassed : Prop
  nontrivialSignalPreserved : Prop
  downstreamPatchAllowed : Prop
  lambdaRetuningAllowed : Prop
  spectraGenerationAllowed : Prop
  observedPlanckRerunAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def carrierProjectionReady (g : MasterRevisedCarrierTangentProjectionGate) : Prop :=
  g.sourceLevelV2Passed /\
  g.carrierThresholdPassed /\
  g.nontrivialSignalPreserved /\
  Not g.downstreamPatchAllowed /\
  Not g.lambdaRetuningAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.observedPlanckRerunAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem revised_carrier_projection_allows_next_diagnostic_only
    (g : MasterRevisedCarrierTangentProjectionGate)
    (hPolicy : carrierProjectionReady g -> g.gatePassed)
    (h : carrierProjectionReady g) :
    g.gatePassed /\ Not g.observedPlanckRerunAllowed /\ Not g.candidatePromotionAllowed := by
  have hGate : g.gatePassed := hPolicy h
  rcases h with âŸ¨_, _, _, _, _, _, hNoRerun, hNoPromotion, _, _âŸ©
  exact âŸ¨hGate, hNoRerun, hNoPromotionâŸ©

end P0EFTJanusZ4MasterRevisedCarrierTangentProjectionGate
end JanusFormal
