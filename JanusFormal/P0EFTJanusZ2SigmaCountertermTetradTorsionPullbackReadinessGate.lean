import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
import JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
import JanusFormal.P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackReadinessGate

set_option autoImplicit false

structure CountertermTetradTorsionPullbackReadinessGate where
  activeEmbeddingFromRadiusGateImported : Prop
  coframeConnectionPullbackGateImported : Prop
  torsionPullbackOnSigmaGateImported : Prop
  orientedPullbackVariationCommutationGateImported : Prop
  torsionVariationTransportGateImported : Prop
  CartanPullbackBibliographyChecked : Prop
  activeEmbeddingReady : Prop
  coframeConnectionPullbackReady : Prop
  orientedPullbackCommutationReady : Prop
  ambientTorsionFormulaReady : Prop
  sigmaTorsionPullbackReady : Prop
  flrwIrreducibleTorsionPullbackReady : Prop
  torsionPullbackOnSigmaReady : Prop
  torsionPullbackVariationAllowedBasisReady : Prop
  torsionPullbackVariationTransportReady : Prop

def torsionPullbackReadinessLedgerDeclared
    (g : CountertermTetradTorsionPullbackReadinessGate) : Prop :=
  g.activeEmbeddingFromRadiusGateImported /\
  g.coframeConnectionPullbackGateImported /\
  g.torsionPullbackOnSigmaGateImported /\
  g.orientedPullbackVariationCommutationGateImported /\
  g.torsionVariationTransportGateImported /\
  g.CartanPullbackBibliographyChecked

def torsionPullbackReadinessReady
    (g : CountertermTetradTorsionPullbackReadinessGate) : Prop :=
  torsionPullbackReadinessLedgerDeclared g /\
  g.activeEmbeddingReady /\
  g.coframeConnectionPullbackReady /\
  g.orientedPullbackCommutationReady /\
  g.ambientTorsionFormulaReady /\
  g.sigmaTorsionPullbackReady /\
  g.flrwIrreducibleTorsionPullbackReady /\
  g.torsionPullbackOnSigmaReady /\
  g.torsionPullbackVariationAllowedBasisReady /\
  g.torsionPullbackVariationTransportReady

theorem torsion_pullback_readiness_requires_active_embedding
    (g : CountertermTetradTorsionPullbackReadinessGate)
    (hReady : torsionPullbackReadinessReady g) :
    g.activeEmbeddingReady := by
  exact hReady.2.1

theorem torsion_pullback_readiness_feeds_variation_transport
    (g : CountertermTetradTorsionPullbackReadinessGate)
    (hReady : torsionPullbackReadinessReady g) :
    g.torsionPullbackVariationTransportReady := by
  exact hReady.2.2.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackReadinessGate
end JanusFormal
