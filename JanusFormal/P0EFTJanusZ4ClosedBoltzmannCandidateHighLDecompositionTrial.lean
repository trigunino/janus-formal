import JanusFormal.P0EFTJanusZ4StandaloneTEEEGRReferenceHandshake

namespace JanusFormal
namespace P0EFTJanusZ4ClosedBoltzmannCandidateHighLDecompositionTrial

set_option autoImplicit false

structure FrozenHighLDecompositionTrial where
  handshakePassed : Prop
  lambdaTLocked : Prop
  lambdaELocked : Prop
  candidateRerunUnchanged : Prop
  noParameterRetuning : Prop
  noNewZ4Physics : Prop
  highlDecompositionExecuted : Prop
  fullPlanckValidation : Prop

def allowedFrozenTrial (t : FrozenHighLDecompositionTrial) : Prop :=
  t.handshakePassed /\
  t.lambdaTLocked /\
  t.lambdaELocked /\
  t.candidateRerunUnchanged /\
  t.noParameterRetuning /\
  t.noNewZ4Physics

theorem allowed_frozen_trial_executes_decomposition
    (t : FrozenHighLDecompositionTrial)
    (hPolicy : allowedFrozenTrial t -> t.highlDecompositionExecuted)
    (h : allowedFrozenTrial t) :
    t.highlDecompositionExecuted := by
  exact hPolicy h

theorem decomposition_trial_is_not_full_planck_validation
    (t : FrozenHighLDecompositionTrial)
    (h : Not t.fullPlanckValidation) :
    Not t.fullPlanckValidation := by
  exact h

end P0EFTJanusZ4ClosedBoltzmannCandidateHighLDecompositionTrial
end JanusFormal
