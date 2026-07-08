import JanusFormal.P0EFTJanusComplexRealityClosedBoundaryTwoCycleGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityActiveEmbeddingOrCompactPhaseGate

set_option autoImplicit false

structure ActiveEmbeddingOrCompactPhaseGate where
  topologicalCycleAuditReady : Prop
  activeEmbeddingReady : Prop
  coframeConnectionPullbackReady : Prop
  activeBoundaryVariationBasisReady : Prop
  omegaSigmaDensityEvaluableOnS2 : Prop
  aroundSigmaZ2CycleClosed : Prop
  compactFramePhaseDerived : Prop
  phasePeriodNormalized : Prop
  kksCrossPairingNonzero : Prop
  alphaGenerated : Prop

def activeEmbeddingRouteReady (g : ActiveEmbeddingOrCompactPhaseGate) : Prop :=
  g.topologicalCycleAuditReady /\
  g.activeEmbeddingReady /\
  g.coframeConnectionPullbackReady /\
  g.activeBoundaryVariationBasisReady /\
  g.omegaSigmaDensityEvaluableOnS2

def compactPhaseRouteReady (g : ActiveEmbeddingOrCompactPhaseGate) : Prop :=
  g.topologicalCycleAuditReady /\
  g.aroundSigmaZ2CycleClosed /\
  g.compactFramePhaseDerived /\
  g.phasePeriodNormalized /\
  g.kksCrossPairingNonzero

def nonzeroKKSBoundaryPeriodRouteReady
    (g : ActiveEmbeddingOrCompactPhaseGate) : Prop :=
  activeEmbeddingRouteReady g \/ compactPhaseRouteReady g

def alphaGeneratedByComplexRealityStateLaw
    (g : ActiveEmbeddingOrCompactPhaseGate) : Prop :=
  nonzeroKKSBoundaryPeriodRouteReady g /\ g.alphaGenerated

theorem both_routes_blocked_blocks_alpha
    (g : ActiveEmbeddingOrCompactPhaseGate)
    (hActive : Not (activeEmbeddingRouteReady g))
    (hPhase : Not (compactPhaseRouteReady g)) :
    Not (alphaGeneratedByComplexRealityStateLaw g) := by
  intro h
  rcases h.left with hA | hP
  · exact hActive hA
  · exact hPhase hP

end P0EFTJanusComplexRealityActiveEmbeddingOrCompactPhaseGate
end JanusFormal
