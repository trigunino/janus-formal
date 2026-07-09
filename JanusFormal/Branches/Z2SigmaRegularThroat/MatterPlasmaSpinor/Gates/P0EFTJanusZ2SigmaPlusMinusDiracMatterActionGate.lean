import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaFermionRouteSelectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBundleProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate

set_option autoImplicit false

structure PlusMinusDiracMatterActionGate where
  curvedDiracActionBibliographyChecked : Prop
  holstFermionBibliographyChecked : Prop
  plusMinusSpinorBundlesDeclared : Prop
  spinorBundleProjectionGateDeclared : Prop
  projectedDiracActionReductionGateDeclared : Prop
  tetradSpinConnectionInputsRequired : Prop
  plusDiracActionDeclared : Prop
  minusDiracActionDeclared : Prop
  z2SigmaProjectionDeclared : Prop
  observationalFitForbidden : Prop
  coframeConnectionPullbackReady : Prop
  plusSpinorDataReady : Prop
  minusSpinorDataReady : Prop
  plusMatterActionReady : Prop
  minusMatterActionReady : Prop
  plusMinusMatterActionsReady : Prop

def plusMinusDiracMatterActionLedgerDeclared
    (g : PlusMinusDiracMatterActionGate) : Prop :=
  g.curvedDiracActionBibliographyChecked /\
  g.holstFermionBibliographyChecked /\
  g.plusMinusSpinorBundlesDeclared /\
  g.spinorBundleProjectionGateDeclared /\
  g.projectedDiracActionReductionGateDeclared /\
  g.tetradSpinConnectionInputsRequired /\
  g.plusDiracActionDeclared /\
  g.minusDiracActionDeclared /\
  g.z2SigmaProjectionDeclared /\
  g.observationalFitForbidden

def plusMinusDiracMatterActionReady
    (g : PlusMinusDiracMatterActionGate) : Prop :=
  plusMinusDiracMatterActionLedgerDeclared g /\
  g.coframeConnectionPullbackReady /\
  g.plusSpinorDataReady /\
  g.minusSpinorDataReady /\
  g.plusMatterActionReady /\
  g.minusMatterActionReady /\
  g.plusMinusMatterActionsReady

theorem dirac_matter_actions_require_coframe_connection
    (g : PlusMinusDiracMatterActionGate)
    (hReady : plusMinusDiracMatterActionReady g) :
    g.coframeConnectionPullbackReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate
end JanusFormal
