import JanusFormal.P0EFTJanusZ4MasterHighLAcousticFailureAutopsyGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterPhotonBaryonMatchingGate

set_option autoImplicit false

structure MasterPhotonBaryonMatchingGate where
  highLAcousticFailureInherited : Prop
  uToTheta0Declared : Prop
  uToDopplerDeclared : Prop
  uToPiDeclared : Prop
  phiPsiMappingDeclared : Prop
  photonBaryonMatchingPassed : Prop
  sourceMappingRequiresRederivation : Prop
  spectraGenerationAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  newPhysicsAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def blockedMatchingReady (g : MasterPhotonBaryonMatchingGate) : Prop :=
  g.highLAcousticFailureInherited /\
  g.uToTheta0Declared /\
  g.uToDopplerDeclared /\
  g.uToPiDeclared /\
  g.phiPsiMappingDeclared /\
  Not g.photonBaryonMatchingPassed /\
  g.sourceMappingRequiresRederivation /\
  Not g.spectraGenerationAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.newPhysicsAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem blocked_matching_forbids_retry
    (g : MasterPhotonBaryonMatchingGate)
    (h : blockedMatchingReady g) :
    Not g.planckRetryAllowed /\ Not g.spectraGenerationAllowed /\
    Not g.retuningAllowed /\ Not g.fullPlanckValidation := by
  rcases h with
    ⟨_, _, _, _, _, _, _, hSpectra, hRetry, _, _, hRetuning, hFull⟩
  exact ⟨hRetry, hSpectra, hRetuning, hFull⟩

end P0EFTJanusZ4MasterPhotonBaryonMatchingGate
end JanusFormal
