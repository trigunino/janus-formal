import JanusFormal.P0EFTJanusComplexRealitySourceFormulaCurationGate
import JanusFormal.P0EFTJanusComplexRealityEq131KKSProjectionGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityCoadjointStateSpaceGate

set_option autoImplicit false

structure CoadjointStateSpaceGate where
  formulaCurationReady : Prop
  eq131ProjectionReady : Prop
  complexMetricDeclared : Prop
  complexPoincareGroupDeclared : Prop
  complexLieAlgebraDeclared : Prop
  momentPairMPDeclared : Prop
  souriauPairingDeclared : Prop
  coadjointActionDeclared : Prop
  ptMassSignSliceDeclared : Prop
  boundaryPhaseSpaceOnSigmaDeclared : Prop
  alphaStateLawReady : Prop

def coadjointStateSpaceReady (g : CoadjointStateSpaceGate) : Prop :=
  g.formulaCurationReady /\
  g.eq131ProjectionReady /\
  g.complexMetricDeclared /\
  g.complexPoincareGroupDeclared /\
  g.complexLieAlgebraDeclared /\
  g.momentPairMPDeclared /\
  g.souriauPairingDeclared /\
  g.coadjointActionDeclared /\
  g.ptMassSignSliceDeclared

def alphaStateLawReady (g : CoadjointStateSpaceGate) : Prop :=
  coadjointStateSpaceReady g /\
  g.boundaryPhaseSpaceOnSigmaDeclared /\
  g.alphaStateLawReady

theorem missing_sigma_boundary_phase_space_blocks_alpha_law
    (g : CoadjointStateSpaceGate)
    (hMissing : Not g.boundaryPhaseSpaceOnSigmaDeclared) :
    Not (alphaStateLawReady g) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusComplexRealityCoadjointStateSpaceGate
end JanusFormal
