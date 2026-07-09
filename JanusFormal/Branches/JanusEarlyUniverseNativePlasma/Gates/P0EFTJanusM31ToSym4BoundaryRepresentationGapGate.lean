import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4DiagonalHamiltonianOrderingAuditGate

namespace JanusFormal
namespace P0EFTJanusM31ToSym4BoundaryRepresentationGapGate

set_option autoImplicit false

structure M31ToSym4BoundaryRepresentationGapGate where
  M31CoadjointTorsorActionAvailable : Prop
  boundaryModeSpaceIdentifiedWithC11 : Prop
  rhoJanusLieToEndC11Derived : Prop
  rhoLiftedToSym4 : Prop
  normalRedshiftHamiltonianSelected : Prop
  orderedSpectrumMapsToAmin : Prop

def M31ToSym4RepresentationClosed
    (g : M31ToSym4BoundaryRepresentationGapGate) : Prop :=
  g.M31CoadjointTorsorActionAvailable /\
  g.boundaryModeSpaceIdentifiedWithC11 /\
  g.rhoJanusLieToEndC11Derived /\
  g.rhoLiftedToSym4 /\
  g.normalRedshiftHamiltonianSelected /\
  g.orderedSpectrumMapsToAmin

def M31ToSym4RepresentationFrontier
    (g : M31ToSym4BoundaryRepresentationGapGate) : Prop :=
  g.M31CoadjointTorsorActionAvailable /\
  g.boundaryModeSpaceIdentifiedWithC11 /\
  Not g.rhoJanusLieToEndC11Derived /\
  Not g.normalRedshiftHamiltonianSelected

theorem torsor_action_without_boundary_representation_blocks_closure
    (g : M31ToSym4BoundaryRepresentationGapGate)
    (hFrontier : M31ToSym4RepresentationFrontier g) :
    Not (M31ToSym4RepresentationClosed g) := by
  intro h
  exact hFrontier.2.2.1 h.2.2.1

end P0EFTJanusM31ToSym4BoundaryRepresentationGapGate
end JanusFormal
