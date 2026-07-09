namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveFLRWSpatialMetricBranchGate

set_option autoImplicit false

structure ActiveFLRWSpatialMetricBranchGate where
  activeCoreZ2Sigma : Prop
  projectiveTunnelTwoFoldTopologyReady : Prop
  topologyAloneFixesSpatialMetricBranch : Prop
  flrwSpatialMetricContractDeclared : Prop
  curvatureSignDomainDeclared : Prop
  curvatureRadiusSymbolDeclared : Prop
  spatialScalarCurvatureRelationDeclared : Prop
  requiresActiveTunnelEmbeddingXPlusMinusOfA : Prop
  requiresActiveInducedSpatialMetricOnFLRWSlices : Prop
  requiresRSigmaOrEmbeddingScale : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  flrwSpatialMetricBranchValuesReady : Prop
  curvatureSignValuesReady : Prop
  curvatureRadiusValuesReady : Prop
  gatePassed : Prop

def spatialMetricBranchPolicyClosed
    (g : ActiveFLRWSpatialMetricBranchGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.projectiveTunnelTwoFoldTopologyReady /\
  Not g.topologyAloneFixesSpatialMetricBranch /\
  g.flrwSpatialMetricContractDeclared /\
  g.curvatureSignDomainDeclared /\
  g.curvatureRadiusSymbolDeclared /\
  g.spatialScalarCurvatureRelationDeclared /\
  g.requiresActiveTunnelEmbeddingXPlusMinusOfA /\
  g.requiresActiveInducedSpatialMetricOnFLRWSlices /\
  g.requiresRSigmaOrEmbeddingScale /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit

theorem topology_alone_does_not_fix_spatial_metric_branch
    (g : ActiveFLRWSpatialMetricBranchGate)
    (h : spatialMetricBranchPolicyClosed g) :
    Not g.topologyAloneFixesSpatialMetricBranch := by
  exact h.2.2.1

theorem branch_values_required_for_gate
    (g : ActiveFLRWSpatialMetricBranchGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.flrwSpatialMetricBranchValuesReady) :
    g.flrwSpatialMetricBranchValuesReady := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaActiveFLRWSpatialMetricBranchGate
end JanusFormal
