namespace JanusFormal
namespace P0EFTDirectCMBTransferScaffold

set_option autoImplicit false

structure DirectCMBTransferScaffold where
  thetaStarProxyReady : Prop
  transferEquationsEncoded : Prop
  backgroundAndRulerInputsReady : Prop
  weylLensingSourceDerived : Prop
  visibilityFunctionDerived : Prop
  boltzmannSolverIntegrated : Prop
  cmbSpectraComputed : Prop

def transferScaffoldReady (c : DirectCMBTransferScaffold) : Prop :=
  c.thetaStarProxyReady /\
  c.transferEquationsEncoded /\
  c.backgroundAndRulerInputsReady

def transferSolverReady (c : DirectCMBTransferScaffold) : Prop :=
  transferScaffoldReady c /\
  c.weylLensingSourceDerived /\
  c.visibilityFunctionDerived /\
  c.boltzmannSolverIntegrated

def directCMBSpectraReady (c : DirectCMBTransferScaffold) : Prop :=
  transferSolverReady c /\
  c.cmbSpectraComputed

theorem transfer_scaffold_closes_equation_interface
    (c : DirectCMBTransferScaffold)
    (hTheta : c.thetaStarProxyReady)
    (hEq : c.transferEquationsEncoded)
    (hInputs : c.backgroundAndRulerInputsReady) :
    transferScaffoldReady c := by
  exact And.intro hTheta (And.intro hEq hInputs)

theorem missing_weyl_source_blocks_transfer_solver
    (c : DirectCMBTransferScaffold)
    (hMissing : Not c.weylLensingSourceDerived) :
    Not (transferSolverReady c) := by
  intro h
  exact hMissing h.right.left

theorem missing_spectra_blocks_direct_cmb
    (c : DirectCMBTransferScaffold)
    (hMissing : Not c.cmbSpectraComputed) :
    Not (directCMBSpectraReady c) := by
  intro h
  exact hMissing h.right

end P0EFTDirectCMBTransferScaffold
end JanusFormal
