import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaSCrossTransportSourceAcceptanceGate
import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaTransportCompatibilitySourceEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSCrossPhiLVariationLawGate

set_option autoImplicit false

structure SCrossPhiLVariationLawGate where
  sCrossTransportSourceAcceptanceGateImported : Prop
  transportCompatibilitySourceEquationGateImported : Prop
  phiMapVariationDeclared : Prop
  lSolderVariationDeclared : Prop
  sectorDiffeomorphismCovarianceDeclared : Prop
  boundaryTermsControlled : Prop
  determinantFactorsKeptOutsideBridge : Prop
  sameBridgeForStressAndQCross : Prop
  noMultiplierRoute : Prop
  independentSCrossFunctionalFound : Prop
  plusPhiLVariationLawDerived : Prop
  minusPhiLVariationLawDerived : Prop
  plusSourceDivergenceEquationDerived : Prop
  minusSourceDivergenceEquationDerived : Prop
  plusTransportCompatibilitySourceDerived : Prop
  minusTransportCompatibilitySourceDerived : Prop

def phiLVariationTemplateDeclared
    (g : SCrossPhiLVariationLawGate) : Prop :=
  g.sCrossTransportSourceAcceptanceGateImported /\
  g.transportCompatibilitySourceEquationGateImported /\
  g.phiMapVariationDeclared /\
  g.lSolderVariationDeclared /\
  g.sectorDiffeomorphismCovarianceDeclared /\
  g.boundaryTermsControlled /\
  g.determinantFactorsKeptOutsideBridge /\
  g.sameBridgeForStressAndQCross /\
  g.noMultiplierRoute

def phiLVariationLawReady
    (g : SCrossPhiLVariationLawGate) : Prop :=
  phiLVariationTemplateDeclared g /\
  g.independentSCrossFunctionalFound /\
  g.plusPhiLVariationLawDerived /\
  g.minusPhiLVariationLawDerived /\
  g.plusSourceDivergenceEquationDerived /\
  g.minusSourceDivergenceEquationDerived /\
  g.plusTransportCompatibilitySourceDerived /\
  g.minusTransportCompatibilitySourceDerived

theorem phi_l_variation_laws_feed_source_divergences
    (g : SCrossPhiLVariationLawGate)
    (hReady : phiLVariationLawReady g) :
    g.plusSourceDivergenceEquationDerived /\
      g.minusSourceDivergenceEquationDerived := by
  exact And.intro hReady.right.right.right.right.left
    hReady.right.right.right.right.right.left

theorem phi_l_variation_laws_feed_transport_compatibility
    (g : SCrossPhiLVariationLawGate)
    (hReady : phiLVariationLawReady g) :
    g.plusTransportCompatibilitySourceDerived /\
      g.minusTransportCompatibilitySourceDerived := by
  exact And.intro hReady.right.right.right.right.right.right.left
    hReady.right.right.right.right.right.right.right

theorem missing_independent_s_cross_blocks_phi_l_law
    (g : SCrossPhiLVariationLawGate)
    (hMissing : Not g.independentSCrossFunctionalFound) :
    Not (phiLVariationLawReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem missing_plus_phi_l_law_blocks_transport_compatibility
    (g : SCrossPhiLVariationLawGate)
    (hMissing : Not g.plusPhiLVariationLawDerived) :
    Not (phiLVariationLawReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

end P0EFTJanusZ2SigmaSCrossPhiLVariationLawGate
end JanusFormal
