import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusRP4PinSignComputationGate
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate

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
  nearestSpinorBundleFrontierDeclared : Prop
  nearestSpinorBundleFrontierDiagnosticOnly : Prop

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
  g.observationalFitForbidden /\
  g.nearestSpinorBundleFrontierDeclared /\
  g.nearestSpinorBundleFrontierDiagnosticOnly

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

theorem nearest_spinor_bundle_frontier_diagnostic_does_not_close_bundle_data
    (g : PlusMinusSpinorBundleDataGate)
    (_hDiag : g.nearestSpinorBundleFrontierDiagnosticOnly)
    (hNoPinLift : Not g.resolvedTunnelPinLiftReady) :
    Not (g.nearestSpinorBundleFrontierDiagnosticOnly /\
      plusMinusSpinorBundleDataReady g) := by
  intro h
  exact hNoPinLift h.2.2.1

end P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate
end JanusFormal
