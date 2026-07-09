import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelInterface

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectiveSpatialSliceTopologyBranchGate

set_option autoImplicit false

structure ProjectiveSpatialSliceTopologyBranchGate where
  activeCoreZ2Sigma : Prop
  globalS4ToRP4CoverReady : Prop
  positiveCurvatureSignSupported : Prop
  rp3SingleInvariantLeafBranchDeclared : Prop
  s3PairedLeafRepresentativeBranchDeclared : Prop
  topologyBranchSelected : Prop
  curvatureSignInputWritten : Prop
  curvatureRadiusStillRequired : Prop
  omegaKNotComputedHere : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  gatePassed : Prop

def branchPolicyClosed
    (g : ProjectiveSpatialSliceTopologyBranchGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.globalS4ToRP4CoverReady /\
  g.positiveCurvatureSignSupported /\
  g.rp3SingleInvariantLeafBranchDeclared /\
  g.s3PairedLeafRepresentativeBranchDeclared /\
  g.curvatureRadiusStillRequired /\
  g.omegaKNotComputedHere /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit

theorem branch_policy_keeps_radius_open
    (g : ProjectiveSpatialSliceTopologyBranchGate)
    (h : branchPolicyClosed g) :
    g.curvatureRadiusStillRequired := by
  exact h.2.2.2.2.2.1

theorem branch_policy_does_not_compute_omega_k
    (g : ProjectiveSpatialSliceTopologyBranchGate)
    (h : branchPolicyClosed g) :
    g.omegaKNotComputedHere := by
  exact h.2.2.2.2.2.2.1

theorem gate_pass_requires_branch_selected
    (g : ProjectiveSpatialSliceTopologyBranchGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.topologyBranchSelected) :
    g.topologyBranchSelected := by
  exact hImplies _hGate

theorem gate_pass_requires_curvature_sign_input
    (g : ProjectiveSpatialSliceTopologyBranchGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.curvatureSignInputWritten) :
    g.curvatureSignInputWritten := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaProjectiveSpatialSliceTopologyBranchGate
end JanusFormal
