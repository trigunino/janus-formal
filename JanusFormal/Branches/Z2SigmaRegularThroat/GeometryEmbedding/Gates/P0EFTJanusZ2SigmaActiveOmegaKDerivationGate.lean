namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveOmegaKDerivationGate

set_option autoImplicit false

structure ActiveOmegaKDerivationGate where
  activeCoreZ2Sigma : Prop
  projectiveTunnelTwoFoldTopologyReady : Prop
  topologyAloneFixesNumericOmegaK : Prop
  omegaKFormulaBuilderReady : Prop
  requiresActiveH0Z2Sigma : Prop
  requiresCurvatureSignKZ2Sigma : Prop
  requiresActiveFLRWCurvatureRadiusOrEmbeddingScale : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalH0Fit : Prop
  omegaKValuesReady : Prop
  gatePassed : Prop

def omegaKDerivationPolicyClosed
    (g : ActiveOmegaKDerivationGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.projectiveTunnelTwoFoldTopologyReady /\
  Not g.topologyAloneFixesNumericOmegaK /\
  g.omegaKFormulaBuilderReady /\
  g.requiresActiveH0Z2Sigma /\
  g.requiresCurvatureSignKZ2Sigma /\
  g.requiresActiveFLRWCurvatureRadiusOrEmbeddingScale /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalH0Fit

theorem topology_alone_does_not_close_omega_k
    (g : ActiveOmegaKDerivationGate)
    (h : omegaKDerivationPolicyClosed g) :
    Not g.topologyAloneFixesNumericOmegaK := by
  exact h.2.2.1

theorem omega_k_values_required_for_gate
    (g : ActiveOmegaKDerivationGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.omegaKValuesReady) :
    g.omegaKValuesReady := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaActiveOmegaKDerivationGate
end JanusFormal
