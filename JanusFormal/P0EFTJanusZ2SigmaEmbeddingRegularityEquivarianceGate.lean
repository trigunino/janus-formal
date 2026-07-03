import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate

set_option autoImplicit false

structure EmbeddingRegularityEquivarianceGate where
  embeddingBibliographyChecked : Prop
  equivariantTubularBibliographyChecked : Prop
  activeTunnelEmbeddingGateDeclared : Prop
  xPlusMinusMapsDeclared : Prop
  regularRadiusConditionDeclared : Prop
  immersionRankTestDeclared : Prop
  injectivityOrTopologicalEmbeddingTestDeclared : Prop
  z2EquivarianceTestDeclared : Prop
  observationalFitForbidden : Prop
  xPlusMinusOfADerived : Prop
  regularThroatRadiusDerived : Prop
  immersionRankDerived : Prop
  topologicalEmbeddingDerived : Prop
  z2EquivariantEmbeddingDerived : Prop
  embeddingRegularityEquivarianceReady : Prop

def embeddingRegularityEquivarianceLedgerDeclared
    (g : EmbeddingRegularityEquivarianceGate) : Prop :=
  g.embeddingBibliographyChecked /\
  g.equivariantTubularBibliographyChecked /\
  g.activeTunnelEmbeddingGateDeclared /\
  g.xPlusMinusMapsDeclared /\
  g.regularRadiusConditionDeclared /\
  g.immersionRankTestDeclared /\
  g.injectivityOrTopologicalEmbeddingTestDeclared /\
  g.z2EquivarianceTestDeclared /\
  g.observationalFitForbidden

def embeddingRegularityEquivarianceReady
    (g : EmbeddingRegularityEquivarianceGate) : Prop :=
  embeddingRegularityEquivarianceLedgerDeclared g /\
  g.xPlusMinusOfADerived /\
  g.regularThroatRadiusDerived /\
  g.immersionRankDerived /\
  g.topologicalEmbeddingDerived /\
  g.z2EquivariantEmbeddingDerived /\
  g.embeddingRegularityEquivarianceReady

theorem embedding_regularity_requires_xpm
    (g : EmbeddingRegularityEquivarianceGate)
    (hReady : embeddingRegularityEquivarianceReady g) :
    g.xPlusMinusOfADerived := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate
end JanusFormal
