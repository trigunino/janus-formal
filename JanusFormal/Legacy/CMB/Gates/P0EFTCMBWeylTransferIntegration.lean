namespace JanusFormal
namespace P0EFTCMBWeylTransferIntegration

set_option autoImplicit false

structure CMBWeylTransferIntegration where
  weylSourceEquationUsed : Prop
  weylTransferIntegrated : Prop
  visibilityPhysical : Prop
  boltzmannHierarchyPhysical : Prop
  clProxyComputed : Prop

def weylTransferIntegrationReady (w : CMBWeylTransferIntegration) : Prop :=
  w.weylSourceEquationUsed /\
  w.weylTransferIntegrated /\
  w.clProxyComputed

def cmbTransferPhysicalReady (w : CMBWeylTransferIntegration) : Prop :=
  weylTransferIntegrationReady w /\
  w.visibilityPhysical /\
  w.boltzmannHierarchyPhysical

theorem weyl_equation_replaces_old_proxy_kernel
    (w : CMBWeylTransferIntegration)
    (hEq : w.weylSourceEquationUsed)
    (hInt : w.weylTransferIntegrated)
    (hCl : w.clProxyComputed) :
    weylTransferIntegrationReady w := by
  exact And.intro hEq (And.intro hInt hCl)

theorem missing_physical_visibility_blocks_physical_cmb_transfer
    (w : CMBWeylTransferIntegration)
    (hMissing : Not w.visibilityPhysical) :
    Not (cmbTransferPhysicalReady w) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBWeylTransferIntegration
end JanusFormal
