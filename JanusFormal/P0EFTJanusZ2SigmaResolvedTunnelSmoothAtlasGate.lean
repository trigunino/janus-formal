import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusZ2SigmaCollarTubularNeighborhoodGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGate

set_option autoImplicit false

structure ResolvedTunnelSmoothAtlasGate where
  tubularNeighborhoodBibliographyChecked : Prop
  collarGluingBibliographyChecked : Prop
  projectiveTunnelInterfaceDeclared : Prop
  collarTubularNeighborhoodGateDeclared : Prop
  frameBundleGateDeclared : Prop
  polarNeighborhoodRemovalDeclared : Prop
  tubularThroatChartDeclared : Prop
  smoothGluingMapDeclared : Prop
  resolvedAtlasDeclared : Prop
  observationalFitForbidden : Prop
  projectiveTunnelTopologyReady : Prop
  collarsDerived : Prop
  tubularReplacementSmoothDerived : Prop
  gluingMapSmoothDerived : Prop
  transitionMapsSmoothDerived : Prop
  resolvedTunnelAtlasDerived : Prop
  smoothAtlasReady : Prop

def resolvedTunnelSmoothAtlasLedgerDeclared
    (g : ResolvedTunnelSmoothAtlasGate) : Prop :=
  g.tubularNeighborhoodBibliographyChecked /\
  g.collarGluingBibliographyChecked /\
  g.projectiveTunnelInterfaceDeclared /\
  g.collarTubularNeighborhoodGateDeclared /\
  g.frameBundleGateDeclared /\
  g.polarNeighborhoodRemovalDeclared /\
  g.tubularThroatChartDeclared /\
  g.smoothGluingMapDeclared /\
  g.resolvedAtlasDeclared /\
  g.observationalFitForbidden

def resolvedTunnelSmoothAtlasReady
    (g : ResolvedTunnelSmoothAtlasGate) : Prop :=
  resolvedTunnelSmoothAtlasLedgerDeclared g /\
  g.projectiveTunnelTopologyReady /\
  g.collarsDerived /\
  g.tubularReplacementSmoothDerived /\
  g.gluingMapSmoothDerived /\
  g.transitionMapsSmoothDerived /\
  g.resolvedTunnelAtlasDerived /\
  g.smoothAtlasReady

theorem smooth_atlas_requires_smooth_gluing
    (g : ResolvedTunnelSmoothAtlasGate)
    (hReady : resolvedTunnelSmoothAtlasReady g) :
    g.gluingMapSmoothDerived := by
  exact hReady.right.right.right.right.left

end P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGate
end JanusFormal
