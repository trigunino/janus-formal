import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTangentNormalOrientationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFluxProjectionDomainGate

set_option autoImplicit false

structure FluxProjectionDomainGate where
  thinShellFluxDomainBibliographyChecked : Prop
  projectiveTunnelSigmaDeclared : Prop
  z2CoorientationSignDeclared : Prop
  inducedMetricNondegeneracyConditionDeclared : Prop
  frameTraceTransportDeclared : Prop
  noIndependentFrameFit : Prop
  observationalFitForbidden : Prop
  coorientationReady : Prop
  resolvedFrameBundleReady : Prop
  regularEmbeddingReady : Prop
  inducedMetricNondegenerateReady : Prop
  embeddingOfAReady : Prop
  sigmaTangentsReady : Prop
  sigmaNormalsReady : Prop
  fluxProjectionDomainReady : Prop

def fluxProjectionDomainLedgerDeclared
    (g : FluxProjectionDomainGate) : Prop :=
  g.thinShellFluxDomainBibliographyChecked /\
  g.projectiveTunnelSigmaDeclared /\
  g.z2CoorientationSignDeclared /\
  g.inducedMetricNondegeneracyConditionDeclared /\
  g.frameTraceTransportDeclared /\
  g.noIndependentFrameFit /\
  g.observationalFitForbidden

def fluxProjectionDomainReady
    (g : FluxProjectionDomainGate) : Prop :=
  fluxProjectionDomainLedgerDeclared g /\
  g.coorientationReady /\
  g.resolvedFrameBundleReady /\
  g.regularEmbeddingReady /\
  g.inducedMetricNondegenerateReady /\
  g.embeddingOfAReady /\
  g.sigmaTangentsReady /\
  g.sigmaNormalsReady /\
  g.fluxProjectionDomainReady

theorem flux_projection_domain_requires_embedding
    (g : FluxProjectionDomainGate)
    (hReady : fluxProjectionDomainReady g) :
    g.embeddingOfAReady := by
  exact hReady.2.2.2.2.2.1

theorem flux_projection_domain_requires_normals
    (g : FluxProjectionDomainGate)
    (hReady : fluxProjectionDomainReady g) :
    g.sigmaNormalsReady := by
  exact hReady.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaFluxProjectionDomainGate
end JanusFormal
