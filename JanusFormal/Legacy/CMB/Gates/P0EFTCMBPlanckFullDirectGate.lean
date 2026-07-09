namespace JanusFormal
namespace P0EFTCMBPlanckFullDirectGate

set_option autoImplicit false

structure PlanckFullDirectGate where
  exactCAMBForkBuilt : Prop
  uncompressedPlanckHighLUsed : Prop
  uncompressedPlanckLowLUsed : Prop
  uncompressedPlanckLensingUsed : Prop
  fullLikelihoodRun : Prop
  observationallyAccepted : Prop

def directCMBLikelihoodReady (g : PlanckFullDirectGate) : Prop :=
  g.exactCAMBForkBuilt /\
  g.uncompressedPlanckHighLUsed /\
  g.uncompressedPlanckLowLUsed /\
  g.uncompressedPlanckLensingUsed /\
  g.fullLikelihoodRun

def fullCMBPredictionAccepted (g : PlanckFullDirectGate) : Prop :=
  directCMBLikelihoodReady g /\
  g.observationallyAccepted

theorem full_likelihood_run_without_acceptance_rejects_branch
    (g : PlanckFullDirectGate)
    (_hReady : directCMBLikelihoodReady g)
    (hRejected : Not g.observationallyAccepted) :
    Not (fullCMBPredictionAccepted g) := by
  intro h
  exact hRejected h.right

end P0EFTCMBPlanckFullDirectGate
end JanusFormal
