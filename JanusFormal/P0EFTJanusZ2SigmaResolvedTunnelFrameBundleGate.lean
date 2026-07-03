import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate

set_option autoImplicit false

structure ResolvedTunnelFrameBundleGate where
  frameBundleBibliographyChecked : Prop
  tubularNeighborhoodBibliographyChecked : Prop
  projectiveTunnelInterfaceDeclared : Prop
  resolvedTunnelSmoothAtlasGateDeclared : Prop
  resolvedTunnelPinLiftGateDeclared : Prop
  resolvedTunnelSmoothManifoldDeclared : Prop
  tangentBundleDeclared : Prop
  frameBundleDeclared : Prop
  plusMinusRestrictionDeclared : Prop
  observationalFitForbidden : Prop
  projectiveTunnelTopologyReady : Prop
  tubularReplacementSmoothDerived : Prop
  resolvedTunnelAtlasDerived : Prop
  resolvedTunnelTangentBundleDerived : Prop
  resolvedTunnelFrameBundleDerived : Prop
  plusFrameBundleRestrictionDerived : Prop
  minusFrameBundleRestrictionDerived : Prop
  resolvedTunnelFrameBundleReady : Prop

def resolvedTunnelFrameBundleLedgerDeclared
    (g : ResolvedTunnelFrameBundleGate) : Prop :=
  g.frameBundleBibliographyChecked /\
  g.tubularNeighborhoodBibliographyChecked /\
  g.projectiveTunnelInterfaceDeclared /\
  g.resolvedTunnelSmoothAtlasGateDeclared /\
  g.resolvedTunnelPinLiftGateDeclared /\
  g.resolvedTunnelSmoothManifoldDeclared /\
  g.tangentBundleDeclared /\
  g.frameBundleDeclared /\
  g.plusMinusRestrictionDeclared /\
  g.observationalFitForbidden

def resolvedTunnelFrameBundleReady
    (g : ResolvedTunnelFrameBundleGate) : Prop :=
  resolvedTunnelFrameBundleLedgerDeclared g /\
  g.projectiveTunnelTopologyReady /\
  g.tubularReplacementSmoothDerived /\
  g.resolvedTunnelAtlasDerived /\
  g.resolvedTunnelTangentBundleDerived /\
  g.resolvedTunnelFrameBundleDerived /\
  g.plusFrameBundleRestrictionDerived /\
  g.minusFrameBundleRestrictionDerived /\
  g.resolvedTunnelFrameBundleReady

theorem frame_bundle_requires_tangent_bundle
    (g : ResolvedTunnelFrameBundleGate)
    (hReady : resolvedTunnelFrameBundleReady g) :
    g.resolvedTunnelTangentBundleDerived := by
  exact hReady.right.right.right.right.left

end P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate
end JanusFormal
