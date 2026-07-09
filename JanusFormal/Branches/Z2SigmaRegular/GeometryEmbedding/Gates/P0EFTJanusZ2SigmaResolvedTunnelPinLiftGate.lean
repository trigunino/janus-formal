import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusRP4PinSignComputationGate
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate

set_option autoImplicit false

structure ResolvedTunnelPinLiftGate where
  spinPinBibliographyChecked : Prop
  projectiveTunnelInterfaceDeclared : Prop
  rp4PinSignGateDeclared : Prop
  sigmaApsPinLiftGateDeclared : Prop
  resolvedTunnelFrameBundleGateDeclared : Prop
  resolvedTunnelFrameBundleDeclared : Prop
  pinLiftCompatibilityCriterionDeclared : Prop
  plusMinusRestrictionCriterionDeclared : Prop
  observationalFitForbidden : Prop
  projectiveTunnelTopologyReady : Prop
  rp4PinPlusReady : Prop
  sigmaApsPinLiftReady : Prop
  resolvedTunnelFrameBundleReady : Prop
  resolvedTunnelPinLiftDerived : Prop
  plusRestrictionPinLiftDerived : Prop
  minusRestrictionPinLiftDerived : Prop
  resolvedTunnelPinLiftReady : Prop
  nearestPinLiftFrontierDeclared : Prop
  nearestPinLiftFrontierDiagnosticOnly : Prop

def resolvedTunnelPinLiftLedgerDeclared
    (g : ResolvedTunnelPinLiftGate) : Prop :=
  g.spinPinBibliographyChecked /\
  g.projectiveTunnelInterfaceDeclared /\
  g.rp4PinSignGateDeclared /\
  g.sigmaApsPinLiftGateDeclared /\
  g.resolvedTunnelFrameBundleGateDeclared /\
  g.resolvedTunnelFrameBundleDeclared /\
  g.pinLiftCompatibilityCriterionDeclared /\
  g.plusMinusRestrictionCriterionDeclared /\
  g.observationalFitForbidden /\
  g.nearestPinLiftFrontierDeclared /\
  g.nearestPinLiftFrontierDiagnosticOnly

def resolvedTunnelPinLiftReady
    (g : ResolvedTunnelPinLiftGate) : Prop :=
  resolvedTunnelPinLiftLedgerDeclared g /\
  g.projectiveTunnelTopologyReady /\
  g.rp4PinPlusReady /\
  g.sigmaApsPinLiftReady /\
  g.resolvedTunnelFrameBundleReady /\
  g.resolvedTunnelPinLiftDerived /\
  g.plusRestrictionPinLiftDerived /\
  g.minusRestrictionPinLiftDerived /\
  g.resolvedTunnelPinLiftReady

theorem resolved_tunnel_pin_lift_requires_sigma_aps_lift
    (g : ResolvedTunnelPinLiftGate)
    (hReady : resolvedTunnelPinLiftReady g) :
    g.sigmaApsPinLiftReady := by
  rcases hReady with ⟨_, _, _, hSigma, _, _, _, _, _⟩
  exact hSigma

theorem resolved_tunnel_pin_lift_requires_frame_bundle
    (g : ResolvedTunnelPinLiftGate)
    (hReady : resolvedTunnelPinLiftReady g) :
    g.resolvedTunnelFrameBundleReady := by
  rcases hReady with ⟨_, _, _, _, hFrame, _, _, _, _⟩
  exact hFrame

theorem nearest_pin_lift_frontier_diagnostic_does_not_close_pin_lift
    (g : ResolvedTunnelPinLiftGate)
    (_hDiag : g.nearestPinLiftFrontierDiagnosticOnly)
    (hNoFrame : Not g.resolvedTunnelFrameBundleReady) :
    Not (g.nearestPinLiftFrontierDiagnosticOnly /\ resolvedTunnelPinLiftReady g) := by
  intro h
  rcases h.2 with ⟨_, _, _, _, hFrame, _, _, _, _⟩
  exact hNoFrame hFrame

end P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate
end JanusFormal
