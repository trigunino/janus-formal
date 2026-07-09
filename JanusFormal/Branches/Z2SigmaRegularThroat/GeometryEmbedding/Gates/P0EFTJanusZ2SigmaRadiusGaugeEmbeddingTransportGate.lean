import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate

set_option autoImplicit false

structure RadiusGaugeEmbeddingTransportGate where
  dynamicThinShellBibliographyChecked : Prop
  activeEmbeddingFromRadiusGateDeclared : Prop
  throatRadiusVariationalGateDeclared : Prop
  embeddingGaugeEquationGateDeclared : Prop
  rSigmaOfAInputDeclared : Prop
  properTimeGaugeInputDeclared : Prop
  radialGaugeInputDeclared : Prop
  xPlusMinusTransportMapDeclared : Prop
  observationalFitForbidden : Prop
  rSigmaOfAReady : Prop
  embeddingGaugeEquationsReady : Prop
  timeGaugeIntegrated : Prop
  radialEmbeddingInserted : Prop
  xPlusMinusOfADerived : Prop
  tangentNormalInputsReady : Prop

def radiusGaugeEmbeddingTransportLedgerDeclared
    (g : RadiusGaugeEmbeddingTransportGate) : Prop :=
  g.dynamicThinShellBibliographyChecked /\
  g.activeEmbeddingFromRadiusGateDeclared /\
  g.throatRadiusVariationalGateDeclared /\
  g.embeddingGaugeEquationGateDeclared /\
  g.rSigmaOfAInputDeclared /\
  g.properTimeGaugeInputDeclared /\
  g.radialGaugeInputDeclared /\
  g.xPlusMinusTransportMapDeclared /\
  g.observationalFitForbidden

def radiusGaugeEmbeddingTransportReady
    (g : RadiusGaugeEmbeddingTransportGate) : Prop :=
  radiusGaugeEmbeddingTransportLedgerDeclared g /\
  g.rSigmaOfAReady /\
  g.embeddingGaugeEquationsReady /\
  g.timeGaugeIntegrated /\
  g.radialEmbeddingInserted /\
  g.xPlusMinusOfADerived /\
  g.tangentNormalInputsReady

theorem transport_requires_radius_law
    (g : RadiusGaugeEmbeddingTransportGate)
    (hReady : radiusGaugeEmbeddingTransportReady g) :
    g.rSigmaOfAReady := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate
end JanusFormal
