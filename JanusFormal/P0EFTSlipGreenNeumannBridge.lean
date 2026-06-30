import JanusFormal.P0EFTSlipJumpDerivation

namespace JanusFormal
namespace P0EFTSlipGreenNeumannBridge

set_option autoImplicit false

structure SlipGreenNeumannBridge where
  derivativeSlipJumpDerived : Prop
  neumannGreenBridgeDefined : Prop
  greenKernelComputed : Prop
  greenKernelEqualsTarget : Prop
  valueSlipDerived : Prop
  lensingSourceClosed : Prop

def valueSlipConditional (s : SlipGreenNeumannBridge) : Prop :=
  s.derivativeSlipJumpDerived /\
  s.neumannGreenBridgeDefined /\
  s.greenKernelComputed /\
  s.greenKernelEqualsTarget /\
  s.valueSlipDerived

def lensingSlipClosed (s : SlipGreenNeumannBridge) : Prop :=
  valueSlipConditional s /\ s.lensingSourceClosed

theorem missing_green_kernel_blocks_value_slip
    (s : SlipGreenNeumannBridge)
    (hMissing : Not s.greenKernelComputed) :
    Not (valueSlipConditional s) := by
  intro h
  exact hMissing h.right.right.left

theorem green_kernel_closes_value_slip
    (s : SlipGreenNeumannBridge)
    (hDeriv : s.derivativeSlipJumpDerived)
    (hBridge : s.neumannGreenBridgeDefined)
    (hKernel : s.greenKernelComputed)
    (hTarget : s.greenKernelEqualsTarget)
    (hValue : s.valueSlipDerived) :
    valueSlipConditional s := by
  exact And.intro hDeriv
    (And.intro hBridge
      (And.intro hKernel
        (And.intro hTarget hValue)))

end P0EFTSlipGreenNeumannBridge
end JanusFormal
