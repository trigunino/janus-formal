import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PolarizationHierarchyClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarSWISWClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeylLensingProjectionClosure

namespace JanusFormal
namespace P0EFTJanusZ4PhysicalClosureTriad

set_option autoImplicit false

structure PhysicalClosureTriad where
  polarizationHierarchyPhysicalReady : Prop
  scalarSWISWPhysicalReady : Prop
  lensingProjectionPhysicalReady : Prop

def cmbZ4PhysicalTriadReady (t : PhysicalClosureTriad) : Prop :=
  t.polarizationHierarchyPhysicalReady /\
  t.scalarSWISWPhysicalReady /\
  t.lensingProjectionPhysicalReady

theorem triad_requires_all_three_locks
    (t : PhysicalClosureTriad)
    (h : cmbZ4PhysicalTriadReady t) :
    t.polarizationHierarchyPhysicalReady /\
    t.scalarSWISWPhysicalReady /\
    t.lensingProjectionPhysicalReady := by
  exact h

theorem missing_lensing_blocks_triad
    (t : PhysicalClosureTriad)
    (hMissing : Not t.lensingProjectionPhysicalReady) :
    Not (cmbZ4PhysicalTriadReady t) := by
  intro h
  exact hMissing h.right.right

end P0EFTJanusZ4PhysicalClosureTriad
end JanusFormal
