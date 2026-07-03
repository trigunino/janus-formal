import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate

set_option autoImplicit false

structure ActiveTunnelEmbeddingOfAGate where
  janusProjectiveTunnelBibliographyChecked : Prop
  thinShellEmbeddingBibliographyChecked : Prop
  resolvedProjectiveTunnelTopologyDeclared : Prop
  activeScaleFactorParameterDeclared : Prop
  xPlusOfADeclared : Prop
  xMinusOfADeclared : Prop
  inducedMetricMatchingOfADeclared : Prop
  z2EquivarianceOfEmbeddingDeclared : Prop
  regularThroatRadiusOfADeclared : Prop
  embeddingFromRadiusGateDeclared : Prop
  xPlusMinusOfADerived : Prop
  deltaKsOfADerived : Prop
  deltaKtauOfADerived : Prop

def activeTunnelEmbeddingProblemDeclared
    (g : ActiveTunnelEmbeddingOfAGate) : Prop :=
  g.janusProjectiveTunnelBibliographyChecked /\
  g.thinShellEmbeddingBibliographyChecked /\
  g.resolvedProjectiveTunnelTopologyDeclared /\
  g.activeScaleFactorParameterDeclared /\
  g.xPlusOfADeclared /\
  g.xMinusOfADeclared /\
  g.inducedMetricMatchingOfADeclared /\
  g.z2EquivarianceOfEmbeddingDeclared /\
  g.regularThroatRadiusOfADeclared /\
  g.embeddingFromRadiusGateDeclared

def activeTunnelEmbeddingOfAClosure
    (g : ActiveTunnelEmbeddingOfAGate) : Prop :=
  activeTunnelEmbeddingProblemDeclared g /\
  g.xPlusMinusOfADerived /\
  g.deltaKsOfADerived /\
  g.deltaKtauOfADerived

theorem deltaK_of_a_requires_xpm_of_a
    (g : ActiveTunnelEmbeddingOfAGate)
    (hReady : activeTunnelEmbeddingOfAClosure g) :
    g.xPlusMinusOfADerived := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate
end JanusFormal
