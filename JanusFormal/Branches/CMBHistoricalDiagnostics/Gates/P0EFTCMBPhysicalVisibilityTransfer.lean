namespace JanusFormal
namespace P0EFTCMBPhysicalVisibilityTransfer

set_option autoImplicit false

structure CMBPhysicalVisibilityTransfer where
  weylSourceEquationUsed : Prop
  physicalVisibilityUsed : Prop
  clProxyComputed : Prop
  boltzmannHierarchyPhysical : Prop

def physicalVisibilityTransferReady (c : CMBPhysicalVisibilityTransfer) : Prop :=
  c.weylSourceEquationUsed /\
  c.physicalVisibilityUsed /\
  c.clProxyComputed

def physicalCMBTransferReady (c : CMBPhysicalVisibilityTransfer) : Prop :=
  physicalVisibilityTransferReady c /\
  c.boltzmannHierarchyPhysical

theorem physical_visibility_replaces_visibility_proxy
    (c : CMBPhysicalVisibilityTransfer)
    (hWeyl : c.weylSourceEquationUsed)
    (hVis : c.physicalVisibilityUsed)
    (hCl : c.clProxyComputed) :
    physicalVisibilityTransferReady c := by
  exact And.intro hWeyl (And.intro hVis hCl)

theorem missing_boltzmann_hierarchy_blocks_physical_transfer
    (c : CMBPhysicalVisibilityTransfer)
    (hMissing : Not c.boltzmannHierarchyPhysical) :
    Not (physicalCMBTransferReady c) := by
  intro h
  exact hMissing h.right

end P0EFTCMBPhysicalVisibilityTransfer
end JanusFormal
