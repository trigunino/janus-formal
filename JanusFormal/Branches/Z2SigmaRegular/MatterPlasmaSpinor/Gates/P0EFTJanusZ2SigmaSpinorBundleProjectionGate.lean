import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusSigmaAPSTraceRegularizationGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinorBundleProjectionGate

set_option autoImplicit false

structure SpinorBundleProjectionGate where
  spinorBundleBibliographyChecked : Prop
  apsBoundarySpinorBibliographyChecked : Prop
  plusMinusSpinorBundleDataGateDeclared : Prop
  boundarySpinorRestrictionGateDeclared : Prop
  spinorBoundaryProjectionMapGateDeclared : Prop
  plusMinusSpinorBundlesDeclared : Prop
  sigmaBoundaryRestrictionDeclared : Prop
  z2SigmaSpinorProjectionDeclared : Prop
  apsPinLiftInputImported : Prop
  observationalFitForbidden : Prop
  plusSpinorBundleReady : Prop
  minusSpinorBundleReady : Prop
  sigmaBoundarySpinorDataReady : Prop
  z2SigmaSpinorProjectionReady : Prop
  plusMinusSpinorProjectionReady : Prop

def spinorBundleProjectionLedgerDeclared
    (g : SpinorBundleProjectionGate) : Prop :=
  g.spinorBundleBibliographyChecked /\
  g.apsBoundarySpinorBibliographyChecked /\
  g.plusMinusSpinorBundleDataGateDeclared /\
  g.boundarySpinorRestrictionGateDeclared /\
  g.spinorBoundaryProjectionMapGateDeclared /\
  g.plusMinusSpinorBundlesDeclared /\
  g.sigmaBoundaryRestrictionDeclared /\
  g.z2SigmaSpinorProjectionDeclared /\
  g.apsPinLiftInputImported /\
  g.observationalFitForbidden

def spinorBundleProjectionReady
    (g : SpinorBundleProjectionGate) : Prop :=
  spinorBundleProjectionLedgerDeclared g /\
  g.plusSpinorBundleReady /\
  g.minusSpinorBundleReady /\
  g.sigmaBoundarySpinorDataReady /\
  g.z2SigmaSpinorProjectionReady /\
  g.plusMinusSpinorProjectionReady

theorem spinor_projection_requires_sigma_boundary_data
    (g : SpinorBundleProjectionGate)
    (hReady : spinorBundleProjectionReady g) :
    g.sigmaBoundarySpinorDataReady := by
  exact hReady.2.2.2.1

theorem spinor_projection_requires_z2_projection
    (g : SpinorBundleProjectionGate)
    (hReady : spinorBundleProjectionReady g) :
    g.z2SigmaSpinorProjectionReady := by
  exact hReady.2.2.2.2.1

end P0EFTJanusZ2SigmaSpinorBundleProjectionGate
end JanusFormal
