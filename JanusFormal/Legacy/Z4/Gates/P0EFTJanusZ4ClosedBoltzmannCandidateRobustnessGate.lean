import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckLikelihoodCompletenessGate

namespace JanusFormal
namespace P0EFTJanusZ4ClosedBoltzmannCandidateRobustnessGate

set_option autoImplicit false

structure ClosedBoltzmannCandidateRobustnessGate where
  bestPointStable : Prop
  localCurvatureDetected : Prop
  lambdaBestNotEdge : Prop
  gainSurvivesLmaxVariation : Prop
  gainSurvivesTCASwitchVariation : Prop
  deltaChi2BelowMinusFive : Prop
  teeeSmoothnessRemainsPass : Prop
  transportGuardsRemainPass : Prop
  lmaxConvergenceRemainsPass : Prop
  gatePassed : Prop
  fullPlanckVerdict : Prop

def robustnessReady (g : ClosedBoltzmannCandidateRobustnessGate) : Prop :=
  g.bestPointStable /\
  g.localCurvatureDetected /\
  g.lambdaBestNotEdge /\
  g.gainSurvivesLmaxVariation /\
  g.gainSurvivesTCASwitchVariation /\
  g.deltaChi2BelowMinusFive /\
  g.teeeSmoothnessRemainsPass /\
  g.transportGuardsRemainPass /\
  g.lmaxConvergenceRemainsPass /\
  Not g.fullPlanckVerdict

theorem ready_implies_robustness_gate
    (g : ClosedBoltzmannCandidateRobustnessGate)
    (hPolicy : robustnessReady g -> g.gatePassed)
    (h : robustnessReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem robust_candidate_is_not_full_planck_verdict
    (g : ClosedBoltzmannCandidateRobustnessGate)
    (h : robustnessReady g) :
    Not g.fullPlanckVerdict := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hNoFull⟩
  exact hNoFull

end P0EFTJanusZ4ClosedBoltzmannCandidateRobustnessGate
end JanusFormal
