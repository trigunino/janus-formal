import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4StrictSourceLevelFrozenCandidateReplayGate

namespace JanusFormal
namespace P0EFTJanusZ4LocalCosmologyProfilingReadinessGate

set_option autoImplicit false

structure LocalCosmologyProfilingReadinessGate where
  regenerativeGRHandshakePassed : Prop
  cacheInvalidationPassed : Prop
  frozenCandidateReplayPassed : Prop
  effectiveZ4SpectrumDeltasRegeneratedPerCosmology : Prop
  sourceLevelZ4DeltasRegeneratedPerCosmology : Prop
  strictSourceLevelFrozenReplayMatches : Prop
  sameNonOverlapAccountingRequired : Prop
  lambdaFrozenForFirstProfile : Prop
  localCosmologyProfilingAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def profilingReadinessReady (g : LocalCosmologyProfilingReadinessGate) : Prop :=
  g.regenerativeGRHandshakePassed /\
  g.cacheInvalidationPassed /\
  g.frozenCandidateReplayPassed /\
  g.effectiveZ4SpectrumDeltasRegeneratedPerCosmology /\
  g.sourceLevelZ4DeltasRegeneratedPerCosmology /\
  g.strictSourceLevelFrozenReplayMatches /\
  g.sameNonOverlapAccountingRequired /\
  g.lambdaFrozenForFirstProfile /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem readiness_ready_allows_local_cosmology_profiling
    (g : LocalCosmologyProfilingReadinessGate)
    (hPolicy : profilingReadinessReady g -> g.localCosmologyProfilingAllowed)
    (h : profilingReadinessReady g) :
    g.localCosmologyProfilingAllowed := by
  exact hPolicy h

theorem missing_source_level_blocks_readiness
    (g : LocalCosmologyProfilingReadinessGate)
    (hMissing : Not g.sourceLevelZ4DeltasRegeneratedPerCosmology) :
    Not (profilingReadinessReady g) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTJanusZ4LocalCosmologyProfilingReadinessGate
end JanusFormal
