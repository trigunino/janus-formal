import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate

set_option autoImplicit false

structure RadiusToEmbeddingConditionalClosureGate where
  thinShellEmbeddingBibliographyChecked : Prop
  radiusGaugeTransportImported : Prop
  embeddingGaugeEquationImported : Prop
  rSigmaInputDeclared : Prop
  properTimeGaugeIntegralDeclared : Prop
  radialEmbeddingInsertionDeclared : Prop
  xPlusMinusConditionalMapDeclared : Prop
  observationalRadiusFitForbidden : Prop
  embeddingGaugeEquationsReady : Prop
  properTimeGaugeIntegratedConditionally : Prop
  radialEmbeddingInsertedConditionally : Prop
  xPlusMinusConditionallyDerived : Prop
  rSigmaOfAReady : Prop
  xPlusMinusOfAReady : Prop

def conditionalEmbeddingLedgerDeclared
    (g : RadiusToEmbeddingConditionalClosureGate) : Prop :=
  g.thinShellEmbeddingBibliographyChecked /\
  g.radiusGaugeTransportImported /\
  g.embeddingGaugeEquationImported /\
  g.rSigmaInputDeclared /\
  g.properTimeGaugeIntegralDeclared /\
  g.radialEmbeddingInsertionDeclared /\
  g.xPlusMinusConditionalMapDeclared /\
  g.observationalRadiusFitForbidden

def radiusToEmbeddingConditionalReady
    (g : RadiusToEmbeddingConditionalClosureGate) : Prop :=
  conditionalEmbeddingLedgerDeclared g /\
  g.embeddingGaugeEquationsReady /\
  g.properTimeGaugeIntegratedConditionally /\
  g.radialEmbeddingInsertedConditionally /\
  g.xPlusMinusConditionallyDerived

def radiusToEmbeddingUnconditionalReady
    (g : RadiusToEmbeddingConditionalClosureGate) : Prop :=
  radiusToEmbeddingConditionalReady g /\
  g.rSigmaOfAReady /\
  g.xPlusMinusOfAReady

theorem unconditional_embedding_requires_radius_law
    (g : RadiusToEmbeddingConditionalClosureGate)
    (hReady : radiusToEmbeddingUnconditionalReady g) :
    g.rSigmaOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate
end JanusFormal
