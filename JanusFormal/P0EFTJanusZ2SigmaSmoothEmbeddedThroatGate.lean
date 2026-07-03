import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate
import JanusFormal.P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate

set_option autoImplicit false

structure SigmaSmoothEmbeddedThroatGate where
  embeddedSubmanifoldBibliographyChecked : Prop
  tubularNeighborhoodPrerequisiteChecked : Prop
  activeTunnelEmbeddingGateDeclared : Prop
  embeddingRegularityEquivarianceGateDeclared : Prop
  sigmaThroatDeclared : Prop
  xPlusMinusEmbeddingDeclared : Prop
  regularRadiusConditionDeclared : Prop
  z2EquivarianceDeclared : Prop
  immersionRankConditionDeclared : Prop
  topologicalEmbeddingConditionDeclared : Prop
  observationalFitForbidden : Prop
  activeTunnelEmbeddingReady : Prop
  regularThroatRadiusDerived : Prop
  immersionRankDerived : Prop
  topologicalEmbeddingDerived : Prop
  z2EquivariantEmbeddingDerived : Prop
  sigmaSmoothEmbeddedThroatDerived : Prop

def sigmaSmoothEmbeddedThroatLedgerDeclared
    (g : SigmaSmoothEmbeddedThroatGate) : Prop :=
  g.embeddedSubmanifoldBibliographyChecked /\
  g.tubularNeighborhoodPrerequisiteChecked /\
  g.activeTunnelEmbeddingGateDeclared /\
  g.embeddingRegularityEquivarianceGateDeclared /\
  g.sigmaThroatDeclared /\
  g.xPlusMinusEmbeddingDeclared /\
  g.regularRadiusConditionDeclared /\
  g.z2EquivarianceDeclared /\
  g.immersionRankConditionDeclared /\
  g.topologicalEmbeddingConditionDeclared /\
  g.observationalFitForbidden

def sigmaSmoothEmbeddedThroatReady
    (g : SigmaSmoothEmbeddedThroatGate) : Prop :=
  sigmaSmoothEmbeddedThroatLedgerDeclared g /\
  g.activeTunnelEmbeddingReady /\
  g.regularThroatRadiusDerived /\
  g.immersionRankDerived /\
  g.topologicalEmbeddingDerived /\
  g.z2EquivariantEmbeddingDerived /\
  g.sigmaSmoothEmbeddedThroatDerived

theorem smooth_embedded_throat_requires_active_embedding
    (g : SigmaSmoothEmbeddedThroatGate)
    (hReady : sigmaSmoothEmbeddedThroatReady g) :
    g.activeTunnelEmbeddingReady := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate
end JanusFormal
