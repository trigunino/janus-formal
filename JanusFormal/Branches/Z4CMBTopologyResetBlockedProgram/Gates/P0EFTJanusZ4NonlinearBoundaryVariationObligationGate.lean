import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4BoundaryVariationClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4VolumeSolderCountertermBridge

namespace JanusFormal
namespace P0EFTJanusZ4NonlinearBoundaryVariationObligationGate

set_option autoImplicit false

structure NonlinearBoundaryVariationObligationGate where
  linearBoundaryResidualCancelled : Prop
  determinantBoundaryResidualCancelled : Prop
  volumeSolderCountertermInserted : Prop
  orientationSingleZ4GeometryFixed : Prop
  nonlinearTetradBoundaryVariationComputed : Prop
  cartanConnectionBoundaryVariationComputed : Prop
  membraneJunctionVariationComputed : Prop
  gaugeFixedBoundaryVariationUnique : Prop
  boundarySecondVariationResidualVanishing : Prop
  fullNonlinearBoundaryVariationClosed : Prop

def nonlinearBoundaryPrerequisitesReady
    (g : NonlinearBoundaryVariationObligationGate) : Prop :=
  g.linearBoundaryResidualCancelled /\
  g.determinantBoundaryResidualCancelled /\
  g.volumeSolderCountertermInserted /\
  g.orientationSingleZ4GeometryFixed

def nonlinearBoundaryAtomicObligationsClosed
    (g : NonlinearBoundaryVariationObligationGate) : Prop :=
  nonlinearBoundaryPrerequisitesReady g /\
  g.nonlinearTetradBoundaryVariationComputed /\
  g.cartanConnectionBoundaryVariationComputed /\
  g.membraneJunctionVariationComputed /\
  g.gaugeFixedBoundaryVariationUnique /\
  g.boundarySecondVariationResidualVanishing

theorem missing_nonlinear_tetrad_boundary_variation_blocks_closure
    (g : NonlinearBoundaryVariationObligationGate)
    (hMissing : Not g.nonlinearTetradBoundaryVariationComputed) :
    Not (nonlinearBoundaryAtomicObligationsClosed g) := by
  intro h
  exact hMissing h.right.left

theorem atomic_boundary_obligations_transport_to_full_closure
    (g : NonlinearBoundaryVariationObligationGate)
    (h : nonlinearBoundaryAtomicObligationsClosed g)
    (hTransport :
      nonlinearBoundaryAtomicObligationsClosed g ->
        g.fullNonlinearBoundaryVariationClosed) :
    g.fullNonlinearBoundaryVariationClosed := by
  exact hTransport h

end P0EFTJanusZ4NonlinearBoundaryVariationObligationGate
end JanusFormal
