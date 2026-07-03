import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusRP4PinSignComputationGate
import JanusFormal.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate

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
  g.observationalFitForbidden

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

end P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate
end JanusFormal
