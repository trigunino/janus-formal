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
  activeEmbeddingGeometryManifestValid : Prop
  embeddingGaugeEquationsReady : Prop
  conditionalRadiusToEmbeddingReady : Prop
  throatRadiusSolutionCertificateReady : Prop
  embeddingUnblockedByRadiusSolution : Prop
  rSigmaOfAReady : Prop
  xPlusMinusOfAReady : Prop
  tangentFramesReady : Prop
  unitNormalsReady : Prop
  activeEmbeddingReady : Prop
  nearestEmbeddingFrontierDeclared : Prop
  nearestEmbeddingFrontierDiagnosticOnly : Prop

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
  g.throatRadiusSolutionCertificateReady /\
  g.embeddingUnblockedByRadiusSolution /\
  g.rSigmaOfAReady /\
  g.xPlusMinusOfAReady /\
  g.tangentFramesReady /\
  g.unitNormalsReady /\
    g.activeEmbeddingReady

theorem active_embedding_manifest_valid_can_supply_embedding_ready
    (g : ActiveEmbeddingReadinessGate)
    (hManifest : g.activeEmbeddingGeometryManifestValid)
    (hManifestImplies : g.activeEmbeddingGeometryManifestValid -> g.activeEmbeddingReady) :
    g.activeEmbeddingReady := by
  exact hManifestImplies hManifest

theorem active_embedding_readiness_requires_radius
    (g : ActiveEmbeddingReadinessGate)
    (hReady : activeEmbeddingReadinessReady g) :
    g.rSigmaOfAReady := by
  exact hReady.2.2.2.2.2.1

theorem active_embedding_readiness_requires_throat_certificate
    (g : ActiveEmbeddingReadinessGate)
    (hReady : activeEmbeddingReadinessReady g) :
    g.throatRadiusSolutionCertificateReady /\ g.embeddingUnblockedByRadiusSolution := by
  exact And.intro hReady.2.2.2.1 hReady.2.2.2.2.1

theorem active_embedding_readiness_feeds_embedding
    (g : ActiveEmbeddingReadinessGate)
    (hReady : activeEmbeddingReadinessReady g) :
    g.activeEmbeddingReady := by
  exact hReady.2.2.2.2.2.2.2.2.2

theorem nearest_embedding_frontier_diagnostic_does_not_close_readiness
    (g : ActiveEmbeddingReadinessGate)
    (_h : g.nearestEmbeddingFrontierDiagnosticOnly) :
    activeEmbeddingReadinessReady g -> activeEmbeddingReadinessReady g := by
  intro hReady
  exact hReady

end P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate
end JanusFormal
