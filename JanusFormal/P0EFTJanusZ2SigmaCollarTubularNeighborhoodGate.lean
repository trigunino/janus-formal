import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCollarTubularNeighborhoodGate

set_option autoImplicit false

structure CollarTubularNeighborhoodGate where
  collarNeighborhoodBibliographyChecked : Prop
  tubularNeighborhoodBibliographyChecked : Prop
  smoothGluingBibliographyChecked : Prop
  projectiveTunnelInterfaceDeclared : Prop
  sigmaSmoothEmbeddedThroatGateDeclared : Prop
  polarNeighborhoodRemovalDeclared : Prop
  sigmaThroatDeclared : Prop
  normalBundleDeclared : Prop
  boundaryCollarsDeclared : Prop
  observationalFitForbidden : Prop
  sigmaSmoothEmbeddedDerived : Prop
  normalBundleDerived : Prop
  plusBoundaryCollarDerived : Prop
  minusBoundaryCollarDerived : Prop
  tubularNeighborhoodDerived : Prop
  collarCompatibilityDerived : Prop
  collarTubularNeighborhoodReady : Prop

def collarTubularNeighborhoodLedgerDeclared
    (g : CollarTubularNeighborhoodGate) : Prop :=
  g.collarNeighborhoodBibliographyChecked /\
  g.tubularNeighborhoodBibliographyChecked /\
  g.smoothGluingBibliographyChecked /\
  g.projectiveTunnelInterfaceDeclared /\
  g.sigmaSmoothEmbeddedThroatGateDeclared /\
  g.polarNeighborhoodRemovalDeclared /\
  g.sigmaThroatDeclared /\
  g.normalBundleDeclared /\
  g.boundaryCollarsDeclared /\
  g.observationalFitForbidden

def collarTubularNeighborhoodReady
    (g : CollarTubularNeighborhoodGate) : Prop :=
  collarTubularNeighborhoodLedgerDeclared g /\
  g.sigmaSmoothEmbeddedDerived /\
  g.normalBundleDerived /\
  g.plusBoundaryCollarDerived /\
  g.minusBoundaryCollarDerived /\
  g.tubularNeighborhoodDerived /\
  g.collarCompatibilityDerived /\
  g.collarTubularNeighborhoodReady

theorem tubular_neighborhood_requires_normal_bundle
    (g : CollarTubularNeighborhoodGate)
    (hReady : collarTubularNeighborhoodReady g) :
    g.normalBundleDerived := by
  exact hReady.right.right.left

end P0EFTJanusZ2SigmaCollarTubularNeighborhoodGate
end JanusFormal
