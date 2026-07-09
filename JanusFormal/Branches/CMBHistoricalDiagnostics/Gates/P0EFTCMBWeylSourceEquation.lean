namespace JanusFormal
namespace P0EFTCMBWeylSourceEquation

set_option autoImplicit false

structure CMBWeylSourceEquation where
  muJanusHolstDerived : Prop
  slipKernelEncoded : Prop
  sigmaLensingResponseEncoded : Prop
  weylSourceEquationReady : Prop
  weylTransferIntegrated : Prop

def weylEquationReady (w : CMBWeylSourceEquation) : Prop :=
  w.muJanusHolstDerived /\
  w.slipKernelEncoded /\
  w.sigmaLensingResponseEncoded /\
  w.weylSourceEquationReady

def weylTransferReady (w : CMBWeylSourceEquation) : Prop :=
  weylEquationReady w /\
  w.weylTransferIntegrated

theorem weyl_source_equation_replaces_kernel_target
    (w : CMBWeylSourceEquation)
    (hMu : w.muJanusHolstDerived)
    (hSlip : w.slipKernelEncoded)
    (hSigma : w.sigmaLensingResponseEncoded)
    (hWeyl : w.weylSourceEquationReady) :
    weylEquationReady w := by
  exact And.intro hMu (And.intro hSlip (And.intro hSigma hWeyl))

theorem missing_weyl_transfer_integration_blocks_cmb_transfer
    (w : CMBWeylSourceEquation)
    (hMissing : Not w.weylTransferIntegrated) :
    Not (weylTransferReady w) := by
  intro h
  exact hMissing h.right

end P0EFTCMBWeylSourceEquation
end JanusFormal
