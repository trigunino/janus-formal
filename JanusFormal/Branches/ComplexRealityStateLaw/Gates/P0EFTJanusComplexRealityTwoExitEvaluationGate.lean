import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityActiveEmbeddingOrCompactPhaseGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityTwoExitEvaluationGate

set_option autoImplicit false

structure TwoExitEvaluationGate where
  activeEmbeddingOnS2Preferred : Prop
  compactPhaseRouteAvailable : Prop
  topologyAloneSufficient : Prop
  physicalBoundaryPhaseSpaceRequired : Prop
  anyExitReadyNow : Prop
  alphaGenerated : Prop

def evaluationClosed (g : TwoExitEvaluationGate) : Prop :=
  g.activeEmbeddingOnS2Preferred /\
  Not g.topologyAloneSufficient /\
  g.physicalBoundaryPhaseSpaceRequired /\
  Not g.anyExitReadyNow /\
  Not g.alphaGenerated

theorem topology_alone_does_not_generate_alpha
    (g : TwoExitEvaluationGate)
    (h : evaluationClosed g) :
    Not g.alphaGenerated := by
  exact h.right.right.right.right

end P0EFTJanusComplexRealityTwoExitEvaluationGate
end JanusFormal
