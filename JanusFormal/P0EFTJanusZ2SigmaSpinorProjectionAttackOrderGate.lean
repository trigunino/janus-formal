import JanusFormal.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinorProjectionAttackOrderGate

set_option autoImplicit false

structure SpinorProjectionAttackOrderGate where
  boundarySpinorRestrictionReady : Prop
  tangentNormalOrientationReady : Prop
  unitNormalCliffordActionReady : Prop
  projectionIdempotentReady : Prop
  projectionSelfAdjointReady : Prop
  spinorBoundaryProjectionMapReady : Prop
  noFreeBoundaryPhase : Prop
  noObservationalSpinorFit : Prop
  noArchivedZ4Projection : Prop

def attackOrderReady (g : SpinorProjectionAttackOrderGate) : Prop :=
  g.boundarySpinorRestrictionReady /\
  g.tangentNormalOrientationReady /\
  g.unitNormalCliffordActionReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.spinorBoundaryProjectionMapReady /\
  g.noFreeBoundaryPhase /\
  g.noObservationalSpinorFit /\
  g.noArchivedZ4Projection

theorem ready_requires_unit_normal_clifford
    (g : SpinorProjectionAttackOrderGate)
    (h : attackOrderReady g) :
    g.unitNormalCliffordActionReady := by
  exact h.2.2.1

theorem ready_forbids_free_projection_inputs
    (g : SpinorProjectionAttackOrderGate)
    (h : attackOrderReady g) :
    g.noFreeBoundaryPhase /\ g.noObservationalSpinorFit /\ g.noArchivedZ4Projection := by
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end P0EFTJanusZ2SigmaSpinorProjectionAttackOrderGate
end JanusFormal
