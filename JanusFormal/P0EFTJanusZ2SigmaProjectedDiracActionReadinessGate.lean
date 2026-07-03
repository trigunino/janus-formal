import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate
import JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackReadinessGate
import JanusFormal.P0EFTJanusZ2SigmaSpinorBundleProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectedDiracActionReadinessGate

set_option autoImplicit false

structure ProjectedDiracActionReadinessGate where
  projectedDiracActionReductionGateImported : Prop
  coframeConnectionPullbackReadinessGateImported : Prop
  spinorBundleProjectionGateImported : Prop
  projectedDiracMatterCurrentGateImported : Prop
  curvedDiracHolstBibliographyChecked : Prop
  curvedDiracActionFormulaReady : Prop
  HolstFermionCouplingFormulaReady : Prop
  coframeConnectionPullbackReady : Prop
  plusMinusSpinorProjectionReady : Prop
  plusDiracActionReduced : Prop
  minusDiracActionReduced : Prop
  z2ProjectedDiracActionReady : Prop
  projectedDiracMatterCurrentReady : Prop

def projectedDiracActionReadinessLedgerDeclared
    (g : ProjectedDiracActionReadinessGate) : Prop :=
  g.projectedDiracActionReductionGateImported /\
  g.coframeConnectionPullbackReadinessGateImported /\
  g.spinorBundleProjectionGateImported /\
  g.projectedDiracMatterCurrentGateImported /\
  g.curvedDiracHolstBibliographyChecked

def projectedDiracActionReadinessReady
    (g : ProjectedDiracActionReadinessGate) : Prop :=
  projectedDiracActionReadinessLedgerDeclared g /\
  g.curvedDiracActionFormulaReady /\
  g.HolstFermionCouplingFormulaReady /\
  g.coframeConnectionPullbackReady /\
  g.plusMinusSpinorProjectionReady /\
  g.plusDiracActionReduced /\
  g.minusDiracActionReduced /\
  g.z2ProjectedDiracActionReady /\
  g.projectedDiracMatterCurrentReady

theorem projected_dirac_action_readiness_requires_pullbacks
    (g : ProjectedDiracActionReadinessGate)
    (hReady : projectedDiracActionReadinessReady g) :
    g.coframeConnectionPullbackReady := by
  exact hReady.2.2.2.1

theorem projected_dirac_action_readiness_feeds_current
    (g : ProjectedDiracActionReadinessGate)
    (hReady : projectedDiracActionReadinessReady g) :
    g.projectedDiracMatterCurrentReady := by
  exact hReady.2.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaProjectedDiracActionReadinessGate
end JanusFormal
