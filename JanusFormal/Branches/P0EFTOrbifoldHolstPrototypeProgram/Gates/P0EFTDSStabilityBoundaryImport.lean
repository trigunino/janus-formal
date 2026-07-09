import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTCosmologyConditionalBridge

namespace JanusFormal
namespace P0EFTDSStabilityBoundaryImport

set_option autoImplicit false

structure DSBoundaryImport where
  boundaryConditionsImported : Prop
  tensorSectorConsistent : Prop
  scalarSpinorBoundaryChannelConsistent : Prop
  vectorBoundaryGhostChecked : Prop
  noVectorBoundaryGhost : Prop

def dsBoundaryImportPartial (d : DSBoundaryImport) : Prop :=
  d.boundaryConditionsImported /\
  d.tensorSectorConsistent /\
  d.scalarSpinorBoundaryChannelConsistent

def dsStabilityConditionallyReady (d : DSBoundaryImport) : Prop :=
  dsBoundaryImportPartial d /\
  d.vectorBoundaryGhostChecked /\
  d.noVectorBoundaryGhost

theorem boundary_import_partially_updates_ds_stability
    (d : DSBoundaryImport)
    (hBoundary : d.boundaryConditionsImported)
    (hTensor : d.tensorSectorConsistent)
    (hScalar : d.scalarSpinorBoundaryChannelConsistent) :
    dsBoundaryImportPartial d := by
  exact And.intro hBoundary (And.intro hTensor hScalar)

theorem missing_vector_audit_blocks_ds_ready
    (d : DSBoundaryImport)
    (hMissing : Not d.vectorBoundaryGhostChecked) :
    Not (dsStabilityConditionallyReady d) := by
  intro h
  exact hMissing h.right.left

theorem vector_audit_closes_ds_stability_conditionally
    (d : DSBoundaryImport)
    (hPartial : dsBoundaryImportPartial d)
    (hChecked : d.vectorBoundaryGhostChecked)
    (hNoGhost : d.noVectorBoundaryGhost) :
    dsStabilityConditionallyReady d := by
  exact And.intro hPartial (And.intro hChecked hNoGhost)

end P0EFTDSStabilityBoundaryImport
end JanusFormal
