namespace JanusFormal
namespace P0EFTNonlocalVisibilityScan

set_option autoImplicit false

structure NonlocalVisibilityScan where
  memoryKernelRun : Prop
  acceptedPointFound : Prop
  kernelGeometricallyDerived : Prop

def visibilityMemoryWindowOpen (s : NonlocalVisibilityScan) : Prop :=
  s.memoryKernelRun /\
  s.acceptedPointFound

def visibilityNoFitReady (s : NonlocalVisibilityScan) : Prop :=
  visibilityMemoryWindowOpen s /\
  s.kernelGeometricallyDerived

theorem accepted_visibility_memory_still_needs_derivation
    (s : NonlocalVisibilityScan)
    (_hOpen : visibilityMemoryWindowOpen s)
    (hMissing : Not s.kernelGeometricallyDerived) :
    Not (visibilityNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTNonlocalVisibilityScan
end JanusFormal
