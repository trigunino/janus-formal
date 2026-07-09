import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4NativeGRDecompositionGate

namespace JanusFormal
namespace P0EFTJanusZ4NativeGRAcousticRepairScan

set_option autoImplicit false

structure AcousticRepairScan where
  z4SectorEnabled : Prop
  projectionOnlyHypothesisTested : Prop
  projectionOnlySufficient : Prop
  nativeSourceRepairRequired : Prop
  z4CorrectionsAllowed : Prop

def scanExecuted (s : AcousticRepairScan) : Prop :=
  Not s.z4SectorEnabled /\ s.projectionOnlyHypothesisTested

theorem failed_projection_scan_requires_source_repair
    (s : AcousticRepairScan)
    (hPolicy : Not s.projectionOnlySufficient -> s.nativeSourceRepairRequired)
    (hFail : Not s.projectionOnlySufficient) :
    s.nativeSourceRepairRequired := by
  exact hPolicy hFail

theorem source_repair_blocks_z4_corrections
    (s : AcousticRepairScan)
    (hPolicy : s.z4CorrectionsAllowed -> Not s.nativeSourceRepairRequired)
    (hRepair : s.nativeSourceRepairRequired) :
    Not s.z4CorrectionsAllowed := by
  intro h
  exact (hPolicy h) hRepair

end P0EFTJanusZ4NativeGRAcousticRepairScan
end JanusFormal
