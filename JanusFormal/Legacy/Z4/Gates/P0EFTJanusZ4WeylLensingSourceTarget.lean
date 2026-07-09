namespace JanusFormal
namespace P0EFTJanusZ4WeylLensingSourceTarget

set_option autoImplicit false

structure WeylLensingSourceTarget where
  weylPotentialDeclared : Prop
  lensingKernelDeclared : Prop
  z4SlipInputsRequired : Prop
  determinantProjectionRequired : Prop
  finiteTransferTargetDeclared : Prop
  sourceCoefficientsDerived : Prop

def weylLensingTargetReady (w : WeylLensingSourceTarget) : Prop :=
  w.weylPotentialDeclared /\
  w.lensingKernelDeclared /\
  w.z4SlipInputsRequired /\
  w.determinantProjectionRequired /\
  w.finiteTransferTargetDeclared

def weylLensingPhysicalReady (w : WeylLensingSourceTarget) : Prop :=
  weylLensingTargetReady w /\
  w.sourceCoefficientsDerived

theorem lensing_target_does_not_imply_physical_sources
    (w : WeylLensingSourceTarget)
    (_ready : weylLensingTargetReady w)
    (hMissing : Not w.sourceCoefficientsDerived) :
    Not (weylLensingPhysicalReady w) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4WeylLensingSourceTarget
end JanusFormal
