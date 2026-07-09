import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterPhotonBaryonMatchingGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterPhotonBaryonAcousticCalculatorGate

set_option autoImplicit false

structure MasterPhotonBaryonAcousticCalculatorGate where
  inputRequiresRederivation : Prop
  oscillatorPhaseDeclared : Prop
  dopplerQuadratureDeclared : Prop
  piQuadrupoleProxyDeclared : Prop
  calculatorDiagnosticReady : Prop
  spectraGenerationAllowed : Prop
  observedLikelihoodAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  newPhysicsAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def diagnosticCalculatorReady (g : MasterPhotonBaryonAcousticCalculatorGate) : Prop :=
  g.inputRequiresRederivation /\
  g.oscillatorPhaseDeclared /\
  g.dopplerQuadratureDeclared /\
  g.piQuadrupoleProxyDeclared /\
  g.calculatorDiagnosticReady /\
  Not g.spectraGenerationAllowed /\
  Not g.observedLikelihoodAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.newPhysicsAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem diagnostic_calculator_does_not_reopen_planck
    (g : MasterPhotonBaryonAcousticCalculatorGate)
    (h : diagnosticCalculatorReady g) :
    Not g.spectraGenerationAllowed /\ Not g.planckRetryAllowed /\
    Not g.retuningAllowed /\ Not g.fullPlanckValidation := by
  rcases h with
    âŸ¨_, _, _, _, _, hSpectra, _, hRetry, _, _, hRetuning, hFullâŸ©
  exact âŸ¨hSpectra, hRetry, hRetuning, hFullâŸ©

end P0EFTJanusZ4MasterPhotonBaryonAcousticCalculatorGate
end JanusFormal
