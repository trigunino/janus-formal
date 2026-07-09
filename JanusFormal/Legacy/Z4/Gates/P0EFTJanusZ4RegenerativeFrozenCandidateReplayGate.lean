import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RegenerativeCacheInvalidationGate

namespace JanusFormal
namespace P0EFTJanusZ4RegenerativeFrozenCandidateReplayGate

set_option autoImplicit false

structure RegenerativeFrozenCandidateReplayGate where
  lambdaFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  z4DeltaSourceReferenceCosmologyReplay : Prop
  checkpointReplayMatches : Prop
  z4DeltasRegeneratedPerCosmology : Prop
  localCosmologyProfilingAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  replayPassed : Prop

def replayReady (g : RegenerativeFrozenCandidateReplayGate) : Prop :=
  g.lambdaFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.z4DeltaSourceReferenceCosmologyReplay /\
  g.checkpointReplayMatches /\
  Not g.z4DeltasRegeneratedPerCosmology /\
  Not g.localCosmologyProfilingAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem replay_ready_passes_gate
    (g : RegenerativeFrozenCandidateReplayGate)
    (hPolicy : replayReady g -> g.replayPassed)
    (h : replayReady g) :
    g.replayPassed := by
  exact hPolicy h

end P0EFTJanusZ4RegenerativeFrozenCandidateReplayGate
end JanusFormal
