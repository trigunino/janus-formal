import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate

set_option autoImplicit false

structure ConnectionOnlyFixedEmbeddingVariationGate where
  embeddingResidualChannelDeclared : Prop
  fieldSpaceSplitBibliographyChecked : Prop
  connectionVariationBasisDeclared : Prop
  embeddingVariationBasisDeclared : Prop
  connectionOnlyVariationDeclared : Prop
  deltaOmegaLeavesEmbeddingFixedDeclared : Prop
  noEmbeddingVariationHiddenInDeltaOmega : Prop
  noFittedVariationMixingCoefficient : Prop
  deltaOmegaXSigmaZeroProved : Prop

def connectionOnlyFixedEmbeddingVariationLedgerDeclared
    (g : ConnectionOnlyFixedEmbeddingVariationGate) : Prop :=
  g.embeddingResidualChannelDeclared /\
  g.fieldSpaceSplitBibliographyChecked /\
  g.connectionVariationBasisDeclared /\
  g.embeddingVariationBasisDeclared /\
  g.connectionOnlyVariationDeclared /\
  g.deltaOmegaLeavesEmbeddingFixedDeclared /\
  g.noEmbeddingVariationHiddenInDeltaOmega /\
  g.noFittedVariationMixingCoefficient

def connectionOnlyFixedEmbeddingVariationReady
    (g : ConnectionOnlyFixedEmbeddingVariationGate) : Prop :=
  connectionOnlyFixedEmbeddingVariationLedgerDeclared g /\
  g.deltaOmegaXSigmaZeroProved

theorem connection_only_variation_implies_delta_x_zero
    (g : ConnectionOnlyFixedEmbeddingVariationGate)
    (hReady : connectionOnlyFixedEmbeddingVariationReady g) :
    g.deltaOmegaXSigmaZeroProved := by
  exact hReady.right

end P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate
end JanusFormal
