import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CandidateLocalCosmologyProfilingGate

namespace JanusFormal
namespace P0EFTJanusZ4RegenerativeCAMBZ4BackendGate

set_option autoImplicit false

structure RegenerativeCAMBZ4BackendGate where
  candidateCosmologyPolicyGatePassed : Prop
  sourceOfSpectraRegenerated : Prop
  backendRegenerative : Prop
  cambGRRegeneratedPerCosmology : Prop
  z4DeltasRegeneratedPerCosmology : Prop
  noStaleCSVReuse : Prop
  cacheKeysIncludeCosmology : Prop
  cacheKeysIncludeNuisance : Prop
  cacheKeysIncludeLambdas : Prop
  cacheKeysIncludeBackendVersions : Prop
  lambdaFrozenInitially : Prop
  noNewPhysics : Prop
  localCosmologyProfilingAllowed : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def regenerativeBackendReady (g : RegenerativeCAMBZ4BackendGate) : Prop :=
  g.candidateCosmologyPolicyGatePassed /\
  g.sourceOfSpectraRegenerated /\
  g.backendRegenerative /\
  g.cambGRRegeneratedPerCosmology /\
  g.z4DeltasRegeneratedPerCosmology /\
  g.noStaleCSVReuse /\
  g.cacheKeysIncludeCosmology /\
  g.cacheKeysIncludeNuisance /\
  g.cacheKeysIncludeLambdas /\
  g.cacheKeysIncludeBackendVersions /\
  g.lambdaFrozenInitially /\
  g.noNewPhysics /\
  Not g.fullPlanckValidation

theorem regenerative_backend_ready_allows_local_cosmology_profiling
    (g : RegenerativeCAMBZ4BackendGate)
    (hPolicy : regenerativeBackendReady g -> g.localCosmologyProfilingAllowed)
    (h : regenerativeBackendReady g) :
    g.localCosmologyProfilingAllowed := by
  exact hPolicy h

theorem csv_fixed_backend_blocks_gate
    (g : RegenerativeCAMBZ4BackendGate)
    (hCSV : Not g.sourceOfSpectraRegenerated) :
    Not (regenerativeBackendReady g) := by
  intro h
  exact hCSV h.right.left

end P0EFTJanusZ4RegenerativeCAMBZ4BackendGate
end JanusFormal
