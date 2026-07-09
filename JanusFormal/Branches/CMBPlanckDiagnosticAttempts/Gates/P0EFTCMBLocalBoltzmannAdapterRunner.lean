namespace JanusFormal
namespace P0EFTCMBLocalBoltzmannAdapterRunner

set_option autoImplicit false

structure CMBLocalBoltzmannAdapterRunner where
  adapterTablesValid : Prop
  localProxyRun : Prop
  externalSolverRun : Prop
  externalValidationPassed : Prop

def localAdapterSmokeTestReady (r : CMBLocalBoltzmannAdapterRunner) : Prop :=
  r.adapterTablesValid /\
  r.localProxyRun

def externalValidationReady (r : CMBLocalBoltzmannAdapterRunner) : Prop :=
  localAdapterSmokeTestReady r /\
  r.externalSolverRun /\
  r.externalValidationPassed

theorem local_runner_smoke_tests_adapter_contract
    (r : CMBLocalBoltzmannAdapterRunner)
    (hTables : r.adapterTablesValid)
    (hRun : r.localProxyRun) :
    localAdapterSmokeTestReady r := by
  exact And.intro hTables hRun

theorem local_runner_does_not_replace_external_solver
    (r : CMBLocalBoltzmannAdapterRunner)
    (hMissing : Not r.externalSolverRun) :
    Not (externalValidationReady r) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBLocalBoltzmannAdapterRunner
end JanusFormal
