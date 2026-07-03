import JanusFormal.P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate
import JanusFormal.P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate
import JanusFormal.P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate
import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate

set_option autoImplicit false

structure ActiveTunnelEmbeddingFromRadiusGate where
  thinShellEmbeddingBibliographyChecked : Prop
  dynamicShellRadiusKinematicsImported : Prop
  radiusGaugeEmbeddingTransportGateDeclared : Prop
  radiusToEmbeddingConditionalClosureImported : Prop
  embeddingGaugeEquationsImported : Prop
  throatRadiusVariationalEquationImported : Prop
  rSigmaToXpmMapDeclared : Prop
  observationalFitForbidden : Prop
  rSigmaOfAReady : Prop
  embeddingGaugeEquationsReady : Prop
  xPlusMinusOfAReady : Prop
  tangentNormalInputsReady : Prop

def activeEmbeddingFromRadiusLedgerDeclared
    (g : ActiveTunnelEmbeddingFromRadiusGate) : Prop :=
  g.thinShellEmbeddingBibliographyChecked /\
  g.dynamicShellRadiusKinematicsImported /\
  g.radiusGaugeEmbeddingTransportGateDeclared /\
  g.radiusToEmbeddingConditionalClosureImported /\
  g.embeddingGaugeEquationsImported /\
  g.throatRadiusVariationalEquationImported /\
  g.rSigmaToXpmMapDeclared /\
  g.observationalFitForbidden

def activeEmbeddingFromRadiusReady
    (g : ActiveTunnelEmbeddingFromRadiusGate) : Prop :=
  activeEmbeddingFromRadiusLedgerDeclared g /\
  g.rSigmaOfAReady /\
  g.embeddingGaugeEquationsReady /\
  g.xPlusMinusOfAReady /\
  g.tangentNormalInputsReady

theorem active_embedding_from_radius_requires_radius_law
    (g : ActiveTunnelEmbeddingFromRadiusGate)
    (hReady : activeEmbeddingFromRadiusReady g) :
    g.rSigmaOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
end JanusFormal
