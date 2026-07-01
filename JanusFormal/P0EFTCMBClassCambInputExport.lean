namespace JanusFormal
namespace P0EFTCMBClassCambInputExport

set_option autoImplicit false

structure CMBClassCambInputExport where
  backgroundTableExported : Prop
  modifiedGravityTableExported : Prop
  visibilityTableExported : Prop
  primordialTableExported : Prop
  externalAdapterWritten : Prop
  externalSolverRun : Prop

def classCambInputExportReady (e : CMBClassCambInputExport) : Prop :=
  e.backgroundTableExported /\
  e.modifiedGravityTableExported /\
  e.visibilityTableExported /\
  e.primordialTableExported

def externalSolverReady (e : CMBClassCambInputExport) : Prop :=
  classCambInputExportReady e /\
  e.externalAdapterWritten /\
  e.externalSolverRun

theorem input_tables_prepare_external_solver_adapter
    (e : CMBClassCambInputExport)
    (hB : e.backgroundTableExported)
    (hMG : e.modifiedGravityTableExported)
    (hV : e.visibilityTableExported)
    (hP : e.primordialTableExported) :
    classCambInputExportReady e := by
  exact And.intro hB (And.intro hMG (And.intro hV hP))

theorem missing_adapter_blocks_external_solver
    (e : CMBClassCambInputExport)
    (hMissing : Not e.externalAdapterWritten) :
    Not (externalSolverReady e) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBClassCambInputExport
end JanusFormal
