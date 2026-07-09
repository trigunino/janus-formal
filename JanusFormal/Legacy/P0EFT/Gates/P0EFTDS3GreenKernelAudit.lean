import JanusFormal.Legacy.P0EFT.Gates.P0EFTSlipGreenNeumannBridge

namespace JanusFormal
namespace P0EFTDS3GreenKernelAudit

set_option autoImplicit false

structure DS3GreenKernelAudit where
  spectralOperatorDefined : Prop
  massGapIdentified : Prop
  kinkOnlyObservableReady : Prop
  coincidentGreenRegularized : Prop
  greenKernelEqualsTarget : Prop
  valueSlipReady : Prop

def kinkBranchReady (g : DS3GreenKernelAudit) : Prop :=
  g.spectralOperatorDefined /\
  g.massGapIdentified /\
  g.kinkOnlyObservableReady

def valueBranchReady (g : DS3GreenKernelAudit) : Prop :=
  kinkBranchReady g /\
  g.coincidentGreenRegularized /\
  g.greenKernelEqualsTarget /\
  g.valueSlipReady

theorem mass_gap_gives_kink_branch
    (g : DS3GreenKernelAudit)
    (hOp : g.spectralOperatorDefined)
    (hGap : g.massGapIdentified)
    (hKink : g.kinkOnlyObservableReady) :
    kinkBranchReady g := by
  exact And.intro hOp (And.intro hGap hKink)

theorem missing_green_regularization_blocks_value_branch
    (g : DS3GreenKernelAudit)
    (hMissing : Not g.coincidentGreenRegularized) :
    Not (valueBranchReady g) := by
  intro h
  exact hMissing h.right.left

theorem missing_kernel_value_blocks_value_branch
    (g : DS3GreenKernelAudit)
    (hMissing : Not g.greenKernelEqualsTarget) :
    Not (valueBranchReady g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTDS3GreenKernelAudit
end JanusFormal
