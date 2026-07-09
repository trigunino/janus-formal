import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusZ2SigmaProjectiveSpatialSliceTopologyBranchGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTimeGaugeLeafActionInputWriterGate

set_option autoImplicit false

structure TimeGaugeLeafActionInputWriterGate where
  activeCoreZ2Sigma : Prop
  z2EquivariantTimeCoordinateDerived : Prop
  timeParityToLeafActionRuleReady : Prop
  observationalTimeGaugeFitForbidden : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  timeGaugeLeafActionInputWritten : Prop
  gatePassed : Prop

def leafActionWriterPolicyClosed
    (g : TimeGaugeLeafActionInputWriterGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.z2EquivariantTimeCoordinateDerived /\
  g.timeParityToLeafActionRuleReady /\
  g.observationalTimeGaugeFitForbidden /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit

theorem gate_pass_requires_leaf_action_input
    (g : TimeGaugeLeafActionInputWriterGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.timeGaugeLeafActionInputWritten) :
    g.timeGaugeLeafActionInputWritten := by
  exact hImplies _hGate

theorem policy_forbids_observational_time_gauge_fit
    (g : TimeGaugeLeafActionInputWriterGate)
    (h : leafActionWriterPolicyClosed g) :
    g.observationalTimeGaugeFitForbidden := by
  exact h.2.2.2.1

end P0EFTJanusZ2SigmaTimeGaugeLeafActionInputWriterGate
end JanusFormal
