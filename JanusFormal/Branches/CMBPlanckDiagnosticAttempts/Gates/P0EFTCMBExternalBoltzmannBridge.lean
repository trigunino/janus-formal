namespace JanusFormal
namespace P0EFTCMBExternalBoltzmannBridge

set_option autoImplicit false

structure CMBExternalBoltzmannBridge where
  bridgeContractWritten : Prop
  proxySpectraAvailable : Prop
  adapterWritten : Prop
  externalSolverRun : Prop
  externalValidationPassed : Prop
  uncompressedLikelihoodReady : Prop

def bridgeReady (b : CMBExternalBoltzmannBridge) : Prop :=
  b.bridgeContractWritten /\
  b.proxySpectraAvailable

def externalCMBValidationReady (b : CMBExternalBoltzmannBridge) : Prop :=
  bridgeReady b /\
  b.adapterWritten /\
  b.externalSolverRun /\
  b.externalValidationPassed /\
  b.uncompressedLikelihoodReady

theorem bridge_contract_prepares_external_validation
    (b : CMBExternalBoltzmannBridge)
    (hContract : b.bridgeContractWritten)
    (hProxy : b.proxySpectraAvailable) :
    bridgeReady b := by
  exact And.intro hContract hProxy

theorem missing_adapter_blocks_external_validation
    (b : CMBExternalBoltzmannBridge)
    (hMissing : Not b.adapterWritten) :
    Not (externalCMBValidationReady b) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBExternalBoltzmannBridge
end JanusFormal
