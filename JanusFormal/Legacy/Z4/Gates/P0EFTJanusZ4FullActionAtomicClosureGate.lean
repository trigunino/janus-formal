import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LinearizedActionVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DeterminantMeasureVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BoundaryVariationClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4FullActionAssemblyTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4FullActionWardClosure

namespace JanusFormal
namespace P0EFTJanusZ4FullActionAtomicClosureGate

set_option autoImplicit false

structure FullActionAtomicClosureGate where
  linearizedActionReady : Prop
  determinantMeasurePhysicalReady : Prop
  fullBoundaryActionClosed : Prop
  assemblyScaffoldReady : Prop
  nonlinearEulerLagrangeResidualVanishing : Prop
  wardClosureReady : Prop
  uniqueActionVariationClosed : Prop

def atomicActionObligationsClosed (g : FullActionAtomicClosureGate) : Prop :=
  g.linearizedActionReady /\
  g.determinantMeasurePhysicalReady /\
  g.fullBoundaryActionClosed /\
  g.assemblyScaffoldReady /\
  g.nonlinearEulerLagrangeResidualVanishing /\
  g.wardClosureReady

theorem atomic_action_obligations_close_unique_action
    (g : FullActionAtomicClosureGate)
    (h : atomicActionObligationsClosed g)
    (hTransport : atomicActionObligationsClosed g -> g.uniqueActionVariationClosed) :
    g.uniqueActionVariationClosed := by
  exact hTransport h

theorem missing_boundary_blocks_atomic_action_closure
    (g : FullActionAtomicClosureGate)
    (hMissing : Not g.fullBoundaryActionClosed) :
    Not (atomicActionObligationsClosed g) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_ward_blocks_atomic_action_closure
    (g : FullActionAtomicClosureGate)
    (hMissing : Not g.wardClosureReady) :
    Not (atomicActionObligationsClosed g) := by
  intro h
  exact hMissing h.right.right.right.right.right

end P0EFTJanusZ4FullActionAtomicClosureGate
end JanusFormal
