import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealitySigmaBoundaryProjectionGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityBoundaryVariationBasisGate

set_option autoImplicit false

structure BoundaryVariationBasisGate where
  sigmaProjectionSymbolicReady : Prop
  normalEmbeddingDisplacementDeclared : Prop
  tangentialGaugeQuotientDeclared : Prop
  frameRotationBoostDeclared : Prop
  connectionHolonomyChannelDeclared : Prop
  activeEmbeddingReady : Prop
  closedBoundaryTwoCycleDeclared : Prop
  alphaGenerated : Prop

def symbolicBoundaryVariationBasisReady (g : BoundaryVariationBasisGate) : Prop :=
  g.sigmaProjectionSymbolicReady /\
  g.normalEmbeddingDisplacementDeclared /\
  g.tangentialGaugeQuotientDeclared /\
  g.frameRotationBoostDeclared /\
  g.connectionHolonomyChannelDeclared

def activeBoundaryVariationBasisReady (g : BoundaryVariationBasisGate) : Prop :=
  symbolicBoundaryVariationBasisReady g /\
  g.activeEmbeddingReady /\
  g.closedBoundaryTwoCycleDeclared

def alphaGeneratedFromBoundaryBasis (g : BoundaryVariationBasisGate) : Prop :=
  activeBoundaryVariationBasisReady g /\ g.alphaGenerated

theorem missing_closed_cycle_blocks_active_basis
    (g : BoundaryVariationBasisGate)
    (hMissing : Not g.closedBoundaryTwoCycleDeclared) :
    Not (activeBoundaryVariationBasisReady g) := by
  intro h
  exact hMissing h.right.right

end P0EFTJanusComplexRealityBoundaryVariationBasisGate
end JanusFormal
