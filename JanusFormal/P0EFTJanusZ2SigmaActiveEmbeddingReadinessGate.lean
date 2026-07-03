import JanusFormal.P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate
import JanusFormal.P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate
import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
import JanusFormal.P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGate
import JanusFormal.P0EFTJanusZ2SigmaTangentNormalOrientationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate

set_option autoImplicit false

structure ActiveEmbeddingReadinessGate where
  radiusGaugeEmbeddingTransportGateImported : Prop
  radiusToEmbeddingConditionalClosureGateImported : Prop
  activeTunnelEmbeddingFromRadiusGateImported : Prop
  embeddingTangentFrameTransportGateImported : Prop
  tangentNormalOrientationGateImported : Prop
  thinShellPrimaryBibliographyChecked : Prop
  embeddingGaugeEquationsReady : Prop
  conditionalRadiusToEmbeddingReady : Prop
  rSigmaOfAReady : Prop
  xPlusMinusOfAReady : Prop
  tangentFramesReady : Prop
  unitNormalsReady : Prop
  activeEmbeddingReady : Prop

def activeEmbeddingReadinessLedgerDeclared
    (g : ActiveEmbeddingReadinessGate) : Prop :=
  g.radiusGaugeEmbeddingTransportGateImported /\
  g.radiusToEmbeddingConditionalClosureGateImported /\
  g.activeTunnelEmbeddingFromRadiusGateImported /\
  g.embeddingTangentFrameTransportGateImported /\
  g.tangentNormalOrientationGateImported /\
  g.thinShellPrimaryBibliographyChecked

def activeEmbeddingReadinessReady
    (g : ActiveEmbeddingReadinessGate) : Prop :=
  activeEmbeddingReadinessLedgerDeclared g /\
  g.embeddingGaugeEquationsReady /\
  g.conditionalRadiusToEmbeddingReady /\
  g.rSigmaOfAReady /\
  g.xPlusMinusOfAReady /\
  g.tangentFramesReady /\
  g.unitNormalsReady /\
  g.activeEmbeddingReady

theorem active_embedding_readiness_requires_radius
    (g : ActiveEmbeddingReadinessGate)
    (hReady : activeEmbeddingReadinessReady g) :
    g.rSigmaOfAReady := by
  exact hReady.2.2.2.1

theorem active_embedding_readiness_feeds_embedding
    (g : ActiveEmbeddingReadinessGate)
    (hReady : activeEmbeddingReadinessReady g) :
    g.activeEmbeddingReady := by
  exact hReady.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate
end JanusFormal
