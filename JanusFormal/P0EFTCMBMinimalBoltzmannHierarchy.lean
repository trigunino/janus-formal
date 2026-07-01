namespace JanusFormal
namespace P0EFTCMBMinimalBoltzmannHierarchy

set_option autoImplicit false

structure CMBMinimalBoltzmannHierarchy where
  weylSourceEquationUsed : Prop
  physicalVisibilityUsed : Prop
  minimalHierarchyIntegrated : Prop
  clProxyComputed : Prop
  fullPhotonBaryonNeutrinoHierarchyValidated : Prop
  planckLikelihoodIntegrated : Prop

def minimalBoltzmannReady (c : CMBMinimalBoltzmannHierarchy) : Prop :=
  c.weylSourceEquationUsed /\
  c.physicalVisibilityUsed /\
  c.minimalHierarchyIntegrated /\
  c.clProxyComputed

def directCMBReady (c : CMBMinimalBoltzmannHierarchy) : Prop :=
  minimalBoltzmannReady c /\
  c.fullPhotonBaryonNeutrinoHierarchyValidated /\
  c.planckLikelihoodIntegrated

theorem minimal_hierarchy_replaces_proxy_transfer_block
    (c : CMBMinimalBoltzmannHierarchy)
    (hWeyl : c.weylSourceEquationUsed)
    (hVis : c.physicalVisibilityUsed)
    (hHierarchy : c.minimalHierarchyIntegrated)
    (hCl : c.clProxyComputed) :
    minimalBoltzmannReady c := by
  exact And.intro hWeyl (And.intro hVis (And.intro hHierarchy hCl))

theorem missing_full_hierarchy_blocks_direct_cmb
    (c : CMBMinimalBoltzmannHierarchy)
    (hMissing : Not c.fullPhotonBaryonNeutrinoHierarchyValidated) :
    Not (directCMBReady c) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBMinimalBoltzmannHierarchy
end JanusFormal
