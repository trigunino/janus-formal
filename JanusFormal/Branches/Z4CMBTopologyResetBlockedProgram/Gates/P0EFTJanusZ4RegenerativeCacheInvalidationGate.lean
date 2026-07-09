import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4RegenerativeGRHandshakeGate

namespace JanusFormal
namespace P0EFTJanusZ4RegenerativeCacheInvalidationGate

set_option autoImplicit false

structure RegenerativeCacheInvalidationGate where
  sourceOfSpectraRegenerated : Prop
  cosmologyHashChangesForAllMutations : Prop
  theoryVectorHashChangesForAllMutations : Prop
  spectraChangeForAllMutations : Prop
  noStaleCSVReuse : Prop
  cacheKeyContainsAllCosmologyParams : Prop
  gatePassed : Prop

def cacheInvalidationReady (g : RegenerativeCacheInvalidationGate) : Prop :=
  g.sourceOfSpectraRegenerated /\
  g.cosmologyHashChangesForAllMutations /\
  g.theoryVectorHashChangesForAllMutations /\
  g.spectraChangeForAllMutations /\
  g.noStaleCSVReuse /\
  g.cacheKeyContainsAllCosmologyParams

theorem cache_invalidation_ready_passes_gate
    (g : RegenerativeCacheInvalidationGate)
    (hPolicy : cacheInvalidationReady g -> g.gatePassed)
    (h : cacheInvalidationReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4RegenerativeCacheInvalidationGate
end JanusFormal
