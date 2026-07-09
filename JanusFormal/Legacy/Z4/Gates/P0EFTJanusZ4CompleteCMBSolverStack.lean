namespace JanusFormal
namespace P0EFTJanusZ4CompleteCMBSolverStack

set_option autoImplicit false

structure CompleteCMBSolverStack where
  boltzmannEvolutionCoreAvailable : Prop
  visibilityRecombinationAvailable : Prop
  weylLineOfSightLensingAvailable : Prop
  unlensedClAvailable : Prop
  clPhiPhiAvailable : Prop
  lensedTTTEEEAvailable : Prop
  perCosmologyRegenerationPassed : Prop
  likelihoodReadyTheoryVectorAvailable : Prop
  observedLikelihoodDiagnosticAllowed : Prop
  observedPlanckValidation : Prop
  candidatePromotionAllowed : Prop
  fullPlanckValidation : Prop

def completeSolverReady (s : CompleteCMBSolverStack) : Prop :=
  s.boltzmannEvolutionCoreAvailable /\
  s.visibilityRecombinationAvailable /\
  s.weylLineOfSightLensingAvailable /\
  s.unlensedClAvailable /\
  s.clPhiPhiAvailable /\
  s.lensedTTTEEEAvailable /\
  s.perCosmologyRegenerationPassed /\
  s.likelihoodReadyTheoryVectorAvailable /\
  s.observedLikelihoodDiagnosticAllowed /\
  Not s.observedPlanckValidation /\
  Not s.candidatePromotionAllowed /\
  Not s.fullPlanckValidation

theorem complete_solver_stack_is_not_planck_validation
    (s : CompleteCMBSolverStack)
    (h : completeSolverReady s) :
    s.likelihoodReadyTheoryVectorAvailable /\ Not s.observedPlanckValidation /\
    Not s.fullPlanckValidation := by
  rcases h with ⟨_, _, _, _, _, _, _, hVector, _, hObserved, _, hFull⟩
  exact ⟨hVector, hObserved, hFull⟩

end P0EFTJanusZ4CompleteCMBSolverStack
end JanusFormal
