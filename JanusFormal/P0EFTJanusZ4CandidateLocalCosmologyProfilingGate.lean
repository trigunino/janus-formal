import JanusFormal.P0EFTJanusZ4CandidateCosmologyParameterPolicyGate

namespace JanusFormal
namespace P0EFTJanusZ4CandidateLocalCosmologyProfilingGate

set_option autoImplicit false

structure LocalCosmologyProfilingGate where
  policyGatePassed : Prop
  sameCosmologySpaceForGRAndCandidate : Prop
  samePriorsBoundsOptimizerForGRAndCandidate : Prop
  lambdaFrozen : Prop
  noNewPhysics : Prop
  cosmologicalTransferRegenerationAvailable : Prop
  localCosmologyProfilingExecuted : Prop
  localCosmologyProfiledCandidate : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def profilingBlockedByStaticSpectraBackend (g : LocalCosmologyProfilingGate) : Prop :=
  g.policyGatePassed /\
  g.sameCosmologySpaceForGRAndCandidate /\
  g.samePriorsBoundsOptimizerForGRAndCandidate /\
  g.lambdaFrozen /\
  g.noNewPhysics /\
  Not g.cosmologicalTransferRegenerationAvailable /\
  Not g.localCosmologyProfilingExecuted /\
  Not g.localCosmologyProfiledCandidate /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem static_spectra_backend_blocks_local_cosmology_profiling
    (g : LocalCosmologyProfilingGate)
    (h : profilingBlockedByStaticSpectraBackend g) :
    Not g.localCosmologyProfiledCandidate := by
  exact h.right.right.right.right.right.right.right.left

end P0EFTJanusZ4CandidateLocalCosmologyProfilingGate
end JanusFormal
