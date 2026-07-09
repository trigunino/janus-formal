import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityCoadjointStateSpaceGate

namespace JanusFormal
namespace P0EFTJanusComplexRealitySigmaBoundaryProjectionGate

set_option autoImplicit false

structure SigmaBoundaryProjectionGate where
  complexCoadjointStateSpaceReady : Prop
  sigmaBoundaryVariationalPackageDeclared : Prop
  embeddingVariationChannelDeclared : Prop
  tetradVariationChannelDeclared : Prop
  connectionVariationChannelDeclared : Prop
  coframePullbackFormulaReady : Prop
  spinConnectionPullbackFormulaReady : Prop
  antiHermitianProjectionPolicyReady : Prop
  activeEmbeddingReady : Prop
  coframePullbackValueReady : Prop
  spinConnectionPullbackValueReady : Prop
  nontrivialBoundaryVariationBasisReady : Prop
  closedBoundaryTwoCycleDeclared : Prop

def symbolicProjectionReady (g : SigmaBoundaryProjectionGate) : Prop :=
  g.complexCoadjointStateSpaceReady /\
  g.sigmaBoundaryVariationalPackageDeclared /\
  g.embeddingVariationChannelDeclared /\
  g.tetradVariationChannelDeclared /\
  g.connectionVariationChannelDeclared /\
  g.coframePullbackFormulaReady /\
  g.spinConnectionPullbackFormulaReady /\
  g.antiHermitianProjectionPolicyReady

def activeProjectionReady (g : SigmaBoundaryProjectionGate) : Prop :=
  symbolicProjectionReady g /\
  g.activeEmbeddingReady /\
  g.coframePullbackValueReady /\
  g.spinConnectionPullbackValueReady /\
  g.nontrivialBoundaryVariationBasisReady /\
  g.closedBoundaryTwoCycleDeclared

theorem symbolic_projection_missing_cycle_blocks_active_projection
    (g : SigmaBoundaryProjectionGate)
    (hMissing : Not g.closedBoundaryTwoCycleDeclared) :
    Not (activeProjectionReady g) := by
  intro h
  exact hMissing h.right.right.right.right.right

end P0EFTJanusComplexRealitySigmaBoundaryProjectionGate
end JanusFormal
