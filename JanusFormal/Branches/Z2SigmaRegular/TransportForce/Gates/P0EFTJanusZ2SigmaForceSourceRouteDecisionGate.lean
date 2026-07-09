import JanusFormal.Branches.Z2SigmaRegular.TransportForce.Gates.P0EFTJanusZ2SigmaSourceForceEquationTargetGate
import JanusFormal.Branches.Z2SigmaRegular.TransportForce.Gates.P0EFTJanusZ2SigmaSCrossTransportSourceAcceptanceGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaForceSourceRouteDecisionGate

set_option autoImplicit false

structure ForceSourceRouteDecisionGate where
  sourceForceEquationTargetGateImported : Prop
  sCrossTransportSourceAcceptanceGateImported : Prop
  activeEmbeddingReadinessGateImported : Prop
  phiLRouteDeclared : Prop
  embeddingRouteDeclared : Prop
  phiLHardBlockerIdentified : Prop
  embeddingHardBlockerIdentified : Prop
  noRouteClosedPrematurely : Prop
  noAuxiliaryRouteArchived : Prop
  embeddingRoutePreferredForNextAttack : Prop
  phiLRouteKeptAsAuxiliary : Prop
  mainBranchNextBlockerUpdated : Prop

def forceSourceRouteDecisionReady
    (g : ForceSourceRouteDecisionGate) : Prop :=
  g.sourceForceEquationTargetGateImported /\
  g.sCrossTransportSourceAcceptanceGateImported /\
  g.activeEmbeddingReadinessGateImported /\
  g.phiLRouteDeclared /\
  g.embeddingRouteDeclared /\
  g.phiLHardBlockerIdentified /\
  g.embeddingHardBlockerIdentified /\
  g.noRouteClosedPrematurely /\
  g.noAuxiliaryRouteArchived /\
  g.embeddingRoutePreferredForNextAttack /\
  g.phiLRouteKeptAsAuxiliary /\
  g.mainBranchNextBlockerUpdated

theorem force_route_decision_keeps_phi_l_auxiliary
    (g : ForceSourceRouteDecisionGate)
    (hReady : forceSourceRouteDecisionReady g) :
    g.phiLRouteKeptAsAuxiliary := by
  exact hReady.right.right.right.right.right.right.right.right.right.right.left

theorem force_route_decision_prefers_embedding_next
    (g : ForceSourceRouteDecisionGate)
    (hReady : forceSourceRouteDecisionReady g) :
    g.embeddingRoutePreferredForNextAttack /\ g.mainBranchNextBlockerUpdated := by
  exact And.intro hReady.right.right.right.right.right.right.right.right.right.left
    hReady.right.right.right.right.right.right.right.right.right.right.right

end P0EFTJanusZ2SigmaForceSourceRouteDecisionGate
end JanusFormal
