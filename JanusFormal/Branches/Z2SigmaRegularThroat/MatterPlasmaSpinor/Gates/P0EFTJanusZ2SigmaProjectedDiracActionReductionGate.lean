import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBundleProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectedDiracActionReductionGate

set_option autoImplicit false

structure ProjectedDiracActionReductionGate where
  curvedDiracActionBibliographyChecked : Prop
  holstFermionCouplingBibliographyChecked : Prop
  coframeConnectionPullbackGateDeclared : Prop
  spinorBundleProjectionGateDeclared : Prop
  plusMinusDiracActionsDeclared : Prop
  z2ProjectedDiracActionDeclared : Prop
  noEffectiveFittedMassOrPhase : Prop
  observationalFitForbidden : Prop
  coframeConnectionPullbackReady : Prop
  plusMinusSpinorProjectionReady : Prop
  plusDiracActionReduced : Prop
  minusDiracActionReduced : Prop
  z2ProjectedDiracActionReady : Prop
  plusMinusMatterActionsReady : Prop

def projectedDiracActionReductionLedgerDeclared
    (g : ProjectedDiracActionReductionGate) : Prop :=
  g.curvedDiracActionBibliographyChecked /\
  g.holstFermionCouplingBibliographyChecked /\
  g.coframeConnectionPullbackGateDeclared /\
  g.spinorBundleProjectionGateDeclared /\
  g.plusMinusDiracActionsDeclared /\
  g.z2ProjectedDiracActionDeclared /\
  g.noEffectiveFittedMassOrPhase /\
  g.observationalFitForbidden

def projectedDiracActionReductionReady
    (g : ProjectedDiracActionReductionGate) : Prop :=
  projectedDiracActionReductionLedgerDeclared g /\
  g.coframeConnectionPullbackReady /\
  g.plusMinusSpinorProjectionReady /\
  g.plusDiracActionReduced /\
  g.minusDiracActionReduced /\
  g.z2ProjectedDiracActionReady /\
  g.plusMinusMatterActionsReady

theorem projected_dirac_reduction_requires_spinor_projection
    (g : ProjectedDiracActionReductionGate)
    (hReady : projectedDiracActionReductionReady g) :
    g.plusMinusSpinorProjectionReady := by
  exact hReady.2.2.1

end P0EFTJanusZ2SigmaProjectedDiracActionReductionGate
end JanusFormal
