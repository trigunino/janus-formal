import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4CandidateLocalNuisanceProfilingGate

namespace JanusFormal
namespace P0EFTJanusZ4BoundarySafeNuisanceProfilingGate

set_option autoImplicit false

structure BoundarySafeNuisanceProfilingGate where
  lambdaFrozen : Prop
  noNewPhysics : Prop
  nonOverlapAccountingOnly : Prop
  sameNuisanceRuleForGRAndCandidate : Prop
  boundarySafeProfileFound : Prop
  combinedGainSurvives : Prop
  decomposedGainSurvives : Prop
  teCostSmall : Prop
  eeNotDegraded : Prop
  boundarySafeLocalProfiledCandidate : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def boundarySafeReady (g : BoundarySafeNuisanceProfilingGate) : Prop :=
  g.lambdaFrozen /\
  g.noNewPhysics /\
  g.nonOverlapAccountingOnly /\
  g.sameNuisanceRuleForGRAndCandidate /\
  g.boundarySafeProfileFound /\
  g.combinedGainSurvives /\
  g.decomposedGainSurvives /\
  g.teCostSmall /\
  g.eeNotDegraded /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem boundary_safe_ready_promotes_candidate
    (g : BoundarySafeNuisanceProfilingGate)
    (hPolicy : boundarySafeReady g -> g.boundarySafeLocalProfiledCandidate)
    (h : boundarySafeReady g) :
    g.boundarySafeLocalProfiledCandidate := by
  exact hPolicy h

end P0EFTJanusZ4BoundarySafeNuisanceProfilingGate
end JanusFormal
