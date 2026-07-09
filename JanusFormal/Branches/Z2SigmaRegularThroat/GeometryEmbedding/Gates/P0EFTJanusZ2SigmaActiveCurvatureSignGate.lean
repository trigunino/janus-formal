namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveCurvatureSignGate

set_option autoImplicit false

structure ActiveCurvatureSignGate where
  activeCoreZ2Sigma : Prop
  projectiveTunnelTwoFoldTopologyReady : Prop
  topologyAloneFixesFLRWCurvatureSign : Prop
  curvatureSignDomainDeclared : Prop
  requiresActiveSpatialMetricBranch : Prop
  requiresActiveEmbeddingScaleOrInducedSpatialMetric : Prop
  requiresRSigmaOrXPlusMinusSolution : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  curvatureSignValuesReady : Prop
  gatePassed : Prop

def curvatureSignPolicyClosed
    (g : ActiveCurvatureSignGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.projectiveTunnelTwoFoldTopologyReady /\
  Not g.topologyAloneFixesFLRWCurvatureSign /\
  g.curvatureSignDomainDeclared /\
  g.requiresActiveSpatialMetricBranch /\
  g.requiresActiveEmbeddingScaleOrInducedSpatialMetric /\
  g.requiresRSigmaOrXPlusMinusSolution /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit

theorem topology_alone_does_not_fix_flrw_curvature_sign
    (g : ActiveCurvatureSignGate)
    (h : curvatureSignPolicyClosed g) :
    Not g.topologyAloneFixesFLRWCurvatureSign := by
  exact h.2.2.1

theorem curvature_sign_values_required_for_gate
    (g : ActiveCurvatureSignGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.curvatureSignValuesReady) :
    g.curvatureSignValuesReady := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaActiveCurvatureSignGate
end JanusFormal
