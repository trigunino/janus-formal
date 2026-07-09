namespace JanusFormal
namespace P0EFTCMBClassCambAdapter

set_option autoImplicit false

structure CMBClassCambAdapter where
  inputTablesExported : Prop
  adapterFilesWritten : Prop
  externalSolverRun : Prop
  externalValidationPassed : Prop
  directCMBLikelihoodReady : Prop

def adapterReady (a : CMBClassCambAdapter) : Prop :=
  a.inputTablesExported /\
  a.adapterFilesWritten

def externalValidationReady (a : CMBClassCambAdapter) : Prop :=
  adapterReady a /\
  a.externalSolverRun /\
  a.externalValidationPassed /\
  a.directCMBLikelihoodReady

theorem written_adapter_prepares_external_run
    (a : CMBClassCambAdapter)
    (hInput : a.inputTablesExported)
    (hAdapter : a.adapterFilesWritten) :
    adapterReady a := by
  exact And.intro hInput hAdapter

theorem missing_external_solver_run_blocks_validation
    (a : CMBClassCambAdapter)
    (hMissing : Not a.externalSolverRun) :
    Not (externalValidationReady a) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBClassCambAdapter
end JanusFormal
