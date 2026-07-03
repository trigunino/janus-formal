import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusRP4PinSignComputationGate
import JanusFormal.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate

set_option autoImplicit false

structure PlusMinusSpinorBundleDataGate where
  spinPinBibliographyChecked : Prop
  rp4PinPlusResultImported : Prop
  projectiveTunnelTopologyImported : Prop
  sigmaApsPinLiftInputImported : Prop
  resolvedTunnelPinLiftGateDeclared : Prop
  plusSectorSpinorBundleDeclared : Prop
  minusSectorSpinorBundleDeclared : Prop
  gravitationalSignSeparatedFromSpinorBundle : Prop
  observationalFitForbidden : Prop
  resolvedTunnelPinLiftReady : Prop
  plusSpinorBundleReady : Prop
  minusSpinorBundleReady : Prop
  plusMinusSpinorBundleDataReady : Prop

def plusMinusSpinorBundleDataLedgerDeclared
    (g : PlusMinusSpinorBundleDataGate) : Prop :=
  g.spinPinBibliographyChecked /\
  g.rp4PinPlusResultImported /\
  g.projectiveTunnelTopologyImported /\
  g.sigmaApsPinLiftInputImported /\
  g.resolvedTunnelPinLiftGateDeclared /\
  g.plusSectorSpinorBundleDeclared /\
  g.minusSectorSpinorBundleDeclared /\
  g.gravitationalSignSeparatedFromSpinorBundle /\
  g.observationalFitForbidden

def plusMinusSpinorBundleDataReady
    (g : PlusMinusSpinorBundleDataGate) : Prop :=
  plusMinusSpinorBundleDataLedgerDeclared g /\
  g.resolvedTunnelPinLiftReady /\
  g.plusSpinorBundleReady /\
  g.minusSpinorBundleReady /\
  g.plusMinusSpinorBundleDataReady

theorem plus_minus_spinor_data_requires_resolved_tunnel_pin_lift
    (g : PlusMinusSpinorBundleDataGate)
    (hReady : plusMinusSpinorBundleDataReady g) :
    g.resolvedTunnelPinLiftReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate
end JanusFormal
