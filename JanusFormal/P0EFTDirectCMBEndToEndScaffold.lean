namespace JanusFormal
namespace P0EFTDirectCMBEndToEndScaffold

set_option autoImplicit false

structure DirectCMBEndToEndScaffold where
  thetaStarProxyReady : Prop
  weylSourceProxyReady : Prop
  visibilityProxyReady : Prop
  boltzmannProxyIntegrated : Prop
  clProxyComputed : Prop
  validatedBoltzmannHierarchyDerived : Prop
  uncompressedPlanckLikelihoodReady : Prop

def cmbProxyPipelineReady (c : DirectCMBEndToEndScaffold) : Prop :=
  c.thetaStarProxyReady /\
  c.weylSourceProxyReady /\
  c.visibilityProxyReady /\
  c.boltzmannProxyIntegrated /\
  c.clProxyComputed

def directCMBLikelihoodReady (c : DirectCMBEndToEndScaffold) : Prop :=
  cmbProxyPipelineReady c /\
  c.validatedBoltzmannHierarchyDerived /\
  c.uncompressedPlanckLikelihoodReady

theorem proxy_pipeline_computes_all_four_requested_blocks
    (c : DirectCMBEndToEndScaffold)
    (hTheta : c.thetaStarProxyReady)
    (hWeyl : c.weylSourceProxyReady)
    (hVis : c.visibilityProxyReady)
    (hBoltz : c.boltzmannProxyIntegrated)
    (hCl : c.clProxyComputed) :
    cmbProxyPipelineReady c := by
  exact And.intro hTheta (And.intro hWeyl (And.intro hVis (And.intro hBoltz hCl)))

theorem proxy_pipeline_is_not_direct_cmb_likelihood_without_validation
    (c : DirectCMBEndToEndScaffold)
    (hMissing : Not c.validatedBoltzmannHierarchyDerived) :
    Not (directCMBLikelihoodReady c) := by
  intro h
  exact hMissing h.right.left

end P0EFTDirectCMBEndToEndScaffold
end JanusFormal
