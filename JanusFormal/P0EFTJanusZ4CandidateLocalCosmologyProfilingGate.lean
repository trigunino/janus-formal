namespace JanusFormal
namespace P0EFTJanusZ4CandidateLocalCosmologyProfilingGate

set_option autoImplicit false

structure LocalCosmologyNuisanceProfilingGate where
  readinessGatePassed : Prop
  sameCosmologySpaceForGRAndCandidate : Prop
  samePriorsBoundsOptimizerForGRAndCandidate : Prop
  sameNuisancePolicyForGRAndCandidate : Prop
  lambdaTFrozen : Prop
  lambdaEFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  overlappingTotalForbidden : Prop
  nonOverlapAccountingOnly : Prop
  profiledGainCombinedHighl : Prop
  profiledGainDecomposedHighl : Prop
  teCostRemainsSmall : Prop
  eeNotDegraded : Prop
  noSevereBoundaryHits : Prop
  transportGuardsPass : Prop
  tcaLmaxGuardsPass : Prop
  localCosmologyNuisanceProfiledEffectiveCandidate : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def localProfileReady (g : LocalCosmologyNuisanceProfilingGate) : Prop :=
  g.readinessGatePassed /\
  g.sameCosmologySpaceForGRAndCandidate /\
  g.samePriorsBoundsOptimizerForGRAndCandidate /\
  g.sameNuisancePolicyForGRAndCandidate /\
  g.lambdaTFrozen /\
  g.lambdaEFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.overlappingTotalForbidden /\
  g.nonOverlapAccountingOnly /\
  g.profiledGainCombinedHighl /\
  g.profiledGainDecomposedHighl /\
  g.teCostRemainsSmall /\
  g.eeNotDegraded /\
  g.noSevereBoundaryHits /\
  g.transportGuardsPass /\
  g.tcaLmaxGuardsPass /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem local_profile_ready_promotes_effective_candidate
    (g : LocalCosmologyNuisanceProfilingGate)
    (hPolicy : localProfileReady g -> g.localCosmologyNuisanceProfiledEffectiveCandidate)
    (h : localProfileReady g) :
    g.localCosmologyNuisanceProfiledEffectiveCandidate := by
  exact hPolicy h

end P0EFTJanusZ4CandidateLocalCosmologyProfilingGate
end JanusFormal
