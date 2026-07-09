import JanusFormal.Legacy.P0EFT.Gates.P0EFTDSStabilityBoundaryImport

namespace JanusFormal
namespace P0EFTDSVectorBoundaryGhostAudit

set_option autoImplicit false

structure DSVectorBoundaryGhostAudit where
  vectorBoundaryGhostChecked : Prop
  noNewLongitudinalBoundaryKineticTerm : Prop
  noVectorBoundaryGhost : Prop
  dsStabilityReadyConditionally : Prop

def vectorAuditClosed (a : DSVectorBoundaryGhostAudit) : Prop :=
  a.vectorBoundaryGhostChecked /\
  a.noNewLongitudinalBoundaryKineticTerm /\
  a.noVectorBoundaryGhost /\
  a.dsStabilityReadyConditionally

theorem no_vector_boundary_ghost_closes_ds_conditionally
    (a : DSVectorBoundaryGhostAudit)
    (hChecked : a.vectorBoundaryGhostChecked)
    (hNoKinetic : a.noNewLongitudinalBoundaryKineticTerm)
    (hNoGhost : a.noVectorBoundaryGhost)
    (hReady : a.dsStabilityReadyConditionally) :
    vectorAuditClosed a := by
  exact And.intro hChecked
    (And.intro hNoKinetic
      (And.intro hNoGhost hReady))

end P0EFTDSVectorBoundaryGhostAudit
end JanusFormal
