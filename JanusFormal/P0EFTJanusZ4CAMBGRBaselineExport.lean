import JanusFormal.P0EFTJanusZ4GRBackendPolicy

namespace JanusFormal
namespace P0EFTJanusZ4CAMBGRBaselineExport

set_option autoImplicit false

structure CAMBGRBaselineExport where
  cambBackendUsed : Prop
  z4SectorEnabled : Prop
  negativeSectorEnabled : Prop
  torsionEnabled : Prop
  nativeSchemaExported : Prop
  finiteSpectraProduced : Prop
  grBaselineExportReady : Prop

def strictGROffExport (e : CAMBGRBaselineExport) : Prop :=
  e.cambBackendUsed /\
  Not e.z4SectorEnabled /\
  Not e.negativeSectorEnabled /\
  Not e.torsionEnabled /\
  e.nativeSchemaExported /\
  e.finiteSpectraProduced

theorem ready_export_follows_strict_gr_off_export
    (e : CAMBGRBaselineExport)
    (hPolicy : strictGROffExport e -> e.grBaselineExportReady)
    (h : strictGROffExport e) :
    e.grBaselineExportReady := by
  exact hPolicy h

end P0EFTJanusZ4CAMBGRBaselineExport
end JanusFormal
