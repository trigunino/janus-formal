import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate
import JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate
import JanusFormal.P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate
import JanusFormal.P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGate

set_option autoImplicit false

structure FixedEmbeddingConnectionPullbackVariationGate where
  activeTunnelEmbeddingGateDeclared : Prop
  coframeConnectionPullbackGateDeclared : Prop
  connectionOnlyFixedEmbeddingVariationGateDeclared : Prop
  fixedMapPullbackVariationCommutationGateDeclared : Prop
  orientedPullbackVariationCommutationGateDeclared : Prop
  differentialFormPullbackNaturalityChecked : Prop
  fixedEmbeddingBranchDeclared : Prop
  connectionVariationBranchDeclared : Prop
  pullbackVariationCommutationDeclared : Prop
  z2OrientationPolicyDeclared : Prop
  noEmbeddingVariationHiddenInDeltaOmega : Prop
  noFittedPullbackCoefficient : Prop
  activeEmbeddingReady : Prop
  connectionPullbackReady : Prop
  fixedEmbeddingConditionProved : Prop
  pullbackCommutesWithDeltaOmega : Prop
  z2OrientedCommutationReady : Prop

def fixedEmbeddingConnectionPullbackVariationLedgerDeclared
    (g : FixedEmbeddingConnectionPullbackVariationGate) : Prop :=
  g.activeTunnelEmbeddingGateDeclared /\
  g.coframeConnectionPullbackGateDeclared /\
  g.connectionOnlyFixedEmbeddingVariationGateDeclared /\
  g.fixedMapPullbackVariationCommutationGateDeclared /\
  g.orientedPullbackVariationCommutationGateDeclared /\
  g.differentialFormPullbackNaturalityChecked /\
  g.fixedEmbeddingBranchDeclared /\
  g.connectionVariationBranchDeclared /\
  g.pullbackVariationCommutationDeclared /\
  g.z2OrientationPolicyDeclared /\
  g.noEmbeddingVariationHiddenInDeltaOmega /\
  g.noFittedPullbackCoefficient

def fixedEmbeddingConnectionPullbackVariationReady
    (g : FixedEmbeddingConnectionPullbackVariationGate) : Prop :=
  fixedEmbeddingConnectionPullbackVariationLedgerDeclared g /\
  g.activeEmbeddingReady /\
  g.connectionPullbackReady /\
  g.fixedEmbeddingConditionProved /\
  g.pullbackCommutesWithDeltaOmega /\
  g.z2OrientedCommutationReady

theorem pullback_variation_ready_requires_fixed_embedding
    (g : FixedEmbeddingConnectionPullbackVariationGate)
    (hReady : fixedEmbeddingConnectionPullbackVariationReady g) :
    g.fixedEmbeddingConditionProved := by
  exact hReady.right.right.right.left

end P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGate
end JanusFormal
