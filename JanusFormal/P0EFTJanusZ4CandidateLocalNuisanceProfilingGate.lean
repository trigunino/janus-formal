import JanusFormal.P0EFTJanusZ4CandidateNuisanceSensitivityGate

namespace JanusFormal
namespace P0EFTJanusZ4CandidateLocalNuisanceProfilingGate

set_option autoImplicit false

structure LocalNuisanceProfilingGate where
  sameNuisanceSpaceForGRAndCandidate : Prop
  samePriorsForGRAndCandidate : Prop
  sameBoundsForGRAndCandidate : Prop
  sameOptimizerForGRAndCandidate : Prop
  lambdaTFrozen : Prop
  lambdaEFrozen : Prop
  noNewPhysics : Prop
  nonOverlapAccounting : Prop
  overlappingTotalForbidden : Prop
  profiledGainCombinedHighl : Prop
  profiledGainDecomposedHighl : Prop
  teCostAfterProfilingSmall : Prop
  eeNotDegradedAfterProfiling : Prop
  nuisanceBestfitNotAtUnphysicalBoundary : Prop
  localProfiledNuisanceEffectiveCandidate : Prop
  fullPlanckValidation : Prop

def profilingReady (g : LocalNuisanceProfilingGate) : Prop :=
  g.sameNuisanceSpaceForGRAndCandidate /\
  g.samePriorsForGRAndCandidate /\
  g.sameBoundsForGRAndCandidate /\
  g.sameOptimizerForGRAndCandidate /\
  g.lambdaTFrozen /\
  g.lambdaEFrozen /\
  g.noNewPhysics /\
  g.nonOverlapAccounting /\
  g.overlappingTotalForbidden /\
  g.profiledGainCombinedHighl /\
  g.profiledGainDecomposedHighl /\
  g.teCostAfterProfilingSmall /\
  g.eeNotDegradedAfterProfiling /\
  g.nuisanceBestfitNotAtUnphysicalBoundary /\
  Not g.fullPlanckValidation

theorem profiling_ready_promotes_local_profiled_candidate
    (g : LocalNuisanceProfilingGate)
    (hPolicy : profilingReady g -> g.localProfiledNuisanceEffectiveCandidate)
    (h : profilingReady g) :
    g.localProfiledNuisanceEffectiveCandidate := by
  exact hPolicy h

end P0EFTJanusZ4CandidateLocalNuisanceProfilingGate
end JanusFormal
