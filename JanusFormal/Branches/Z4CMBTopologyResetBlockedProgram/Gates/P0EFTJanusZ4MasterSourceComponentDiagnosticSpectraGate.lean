import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterPhotonBaryonMatchingGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterSourceComponentDiagnosticSpectraGate

set_option autoImplicit false

structure MasterSourceComponentDiagnosticSpectraGate where
  surfaceSWComponentWritten : Prop
  earlyISWComponentWritten : Prop
  dopplerComponentWritten : Prop
  polarizationPiComponentWritten : Prop
  lensWeylComponentWritten : Prop
  sourceComponentAttributionComplete : Prop
  unlensedLensedSplitAvailable : Prop
  observedLikelihoodAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  newPhysicsAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def diagnosticComponentsReady (g : MasterSourceComponentDiagnosticSpectraGate) : Prop :=
  g.surfaceSWComponentWritten /\
  g.earlyISWComponentWritten /\
  g.dopplerComponentWritten /\
  g.polarizationPiComponentWritten /\
  g.lensWeylComponentWritten /\
  g.sourceComponentAttributionComplete /\
  Not g.observedLikelihoodAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.newPhysicsAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem diagnostic_components_do_not_validate_planck
    (g : MasterSourceComponentDiagnosticSpectraGate)
    (h : diagnosticComponentsReady g) :
    Not g.observedLikelihoodAllowed /\ Not g.planckRetryAllowed /\ Not g.fullPlanckValidation := by
  rcases h with
    âŸ¨_, _, _, _, _, _, hLikelihood, hRetry, _, _, _, hFullâŸ©
  exact âŸ¨hLikelihood, hRetry, hFullâŸ©

end P0EFTJanusZ4MasterSourceComponentDiagnosticSpectraGate
end JanusFormal
