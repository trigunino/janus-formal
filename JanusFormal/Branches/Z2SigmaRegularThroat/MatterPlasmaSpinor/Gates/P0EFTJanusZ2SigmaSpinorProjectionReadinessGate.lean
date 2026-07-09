import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBundleProjectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinorProjectionReadinessGate

set_option autoImplicit false

structure SpinorProjectionReadinessGate where
  spinorBundleProjectionGateImported : Prop
  plusMinusSpinorBundleDataGateImported : Prop
  boundarySpinorRestrictionGateImported : Prop
  spinorBoundaryProjectionMapGateImported : Prop
  resolvedTunnelPinLiftGateImported : Prop
  spinorProjectionBibliographyChecked : Prop
  genericSpinorBundleRestrictionReady : Prop
  genericAPSProjectionFormulaReady : Prop
  resolvedTunnelPinLiftReady : Prop
  plusMinusSpinorBundleDataReady : Prop
  sigmaBoundarySpinorDataReady : Prop
  z2SigmaProjectionMapReady : Prop
  plusMinusSpinorProjectionReady : Prop

def spinorProjectionReadinessLedgerDeclared
    (g : SpinorProjectionReadinessGate) : Prop :=
  g.spinorBundleProjectionGateImported /\
  g.plusMinusSpinorBundleDataGateImported /\
  g.boundarySpinorRestrictionGateImported /\
  g.spinorBoundaryProjectionMapGateImported /\
  g.resolvedTunnelPinLiftGateImported /\
  g.spinorProjectionBibliographyChecked

def spinorProjectionReadinessReady
    (g : SpinorProjectionReadinessGate) : Prop :=
  spinorProjectionReadinessLedgerDeclared g /\
  g.genericSpinorBundleRestrictionReady /\
  g.genericAPSProjectionFormulaReady /\
  g.resolvedTunnelPinLiftReady /\
  g.plusMinusSpinorBundleDataReady /\
  g.sigmaBoundarySpinorDataReady /\
  g.z2SigmaProjectionMapReady /\
  g.plusMinusSpinorProjectionReady

theorem spinor_projection_readiness_requires_pin_lift
    (g : SpinorProjectionReadinessGate)
    (hReady : spinorProjectionReadinessReady g) :
    g.resolvedTunnelPinLiftReady := by
  exact hReady.2.2.2.1

theorem spinor_projection_readiness_feeds_projected_dirac_action
    (g : SpinorProjectionReadinessGate)
    (hReady : spinorProjectionReadinessReady g) :
    g.plusMinusSpinorProjectionReady := by
  exact hReady.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaSpinorProjectionReadinessGate
end JanusFormal
