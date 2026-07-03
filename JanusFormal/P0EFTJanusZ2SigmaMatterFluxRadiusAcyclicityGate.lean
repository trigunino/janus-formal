import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
import JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate
import JanusFormal.P0EFTJanusZ2SigmaMatterFluxFrontierGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGate

set_option autoImplicit false

structure MatterFluxRadiusAcyclicityGate where
  matterFluxFrontierImported : Prop
  coupledRadiusFluxSystemImported : Prop
  activeEmbeddingFromRadiusImported : Prop
  thinShellFluxBibliographyChecked : Prop
  activeProjectionUsesEmbeddingDeclared : Prop
  embeddingDependsOnRSigmaDeclared : Prop
  independentFluxSourceForRadiusForbidden : Prop
  transparencyMayBeAcyclicIfDerivedIndependently : Prop
  coupledRadiusFluxRouteDeclared : Prop
  transparencyAcyclicReady : Prop
  activeProjectionAcyclicReady : Prop
  coupledRadiusFluxSystemReady : Prop
  matterFluxCanEnterRadiusSolution : Prop

def matterFluxRadiusAcyclicityLedgerDeclared
    (g : MatterFluxRadiusAcyclicityGate) : Prop :=
  g.matterFluxFrontierImported /\
  g.coupledRadiusFluxSystemImported /\
  g.activeEmbeddingFromRadiusImported /\
  g.thinShellFluxBibliographyChecked /\
  g.activeProjectionUsesEmbeddingDeclared /\
  g.embeddingDependsOnRSigmaDeclared /\
  g.independentFluxSourceForRadiusForbidden /\
  g.transparencyMayBeAcyclicIfDerivedIndependently /\
  g.coupledRadiusFluxRouteDeclared

def matterFluxRadiusAcyclicRouteReady
    (g : MatterFluxRadiusAcyclicityGate) : Prop :=
  matterFluxRadiusAcyclicityLedgerDeclared g /\
  (g.transparencyAcyclicReady \/ g.coupledRadiusFluxSystemReady) /\
  g.matterFluxCanEnterRadiusSolution

theorem active_projection_alone_does_not_close_radius_source
    (g : MatterFluxRadiusAcyclicityGate)
    (hReady : matterFluxRadiusAcyclicRouteReady g) :
    g.transparencyAcyclicReady \/ g.coupledRadiusFluxSystemReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGate
end JanusFormal
