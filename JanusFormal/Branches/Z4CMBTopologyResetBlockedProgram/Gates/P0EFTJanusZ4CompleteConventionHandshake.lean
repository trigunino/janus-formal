import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CompleteCMBSolverStack

namespace JanusFormal
namespace P0EFTJanusZ4CompleteConventionHandshake

set_option autoImplicit false

structure CompleteConventionHandshake where
  clConventionCalibrationPassed : Prop
  grReferenceConventionHandshakePassed : Prop
  likelihoodReadyTheoryVectorAvailable : Prop
  observedLikelihoodDiagnosticAllowed : Prop
  observedPlanckValidation : Prop
  candidatePromotionAllowed : Prop
  fullPlanckValidation : Prop

def conventionHandshakeReady (g : CompleteConventionHandshake) : Prop :=
  g.clConventionCalibrationPassed /\
  g.grReferenceConventionHandshakePassed /\
  g.likelihoodReadyTheoryVectorAvailable /\
  g.observedLikelihoodDiagnosticAllowed /\
  Not g.observedPlanckValidation /\
  Not g.candidatePromotionAllowed /\
  Not g.fullPlanckValidation

theorem convention_handshake_is_not_validation
    (g : CompleteConventionHandshake)
    (h : conventionHandshakeReady g) :
    g.observedLikelihoodDiagnosticAllowed /\ Not g.observedPlanckValidation /\
    Not g.fullPlanckValidation := by
  rcases h with âŸ¨_, _, _, hDiagnostic, hObserved, _, hFullâŸ©
  exact âŸ¨hDiagnostic, hObserved, hFullâŸ©

end P0EFTJanusZ4CompleteConventionHandshake
end JanusFormal
