import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate
import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusLawGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate

set_option autoImplicit false

structure CountertermEmbeddingResidualChannelGate where
  activeTunnelEmbeddingOfAGateDeclared : Prop
  tunnelEmbeddingExtrinsicCurvatureGateDeclared : Prop
  throatRadiusLawGateDeclared : Prop
  shellEmbeddingVariationBibliographyChecked : Prop
  embeddingResidualChannelProblemDeclared : Prop
  deltaXVariationBasisDeclared : Prop
  deltaXToDeltaHDeltaKTransportDeclared : Prop
  z2OrientationTransportDeclared : Prop
  noFittedEmbeddingResidualCoefficient : Prop
  embeddingResidualCoefficientExplicit : Prop
  embeddingResidualInAllowedBasis : Prop
  embeddingResidualReadyForOneFormDecomposition : Prop

def countertermEmbeddingResidualChannelLedgerDeclared
    (g : CountertermEmbeddingResidualChannelGate) : Prop :=
  g.activeTunnelEmbeddingOfAGateDeclared /\
  g.tunnelEmbeddingExtrinsicCurvatureGateDeclared /\
  g.throatRadiusLawGateDeclared /\
  g.shellEmbeddingVariationBibliographyChecked /\
  g.embeddingResidualChannelProblemDeclared /\
  g.deltaXVariationBasisDeclared /\
  g.deltaXToDeltaHDeltaKTransportDeclared /\
  g.z2OrientationTransportDeclared /\
  g.noFittedEmbeddingResidualCoefficient

def countertermEmbeddingResidualChannelReady
    (g : CountertermEmbeddingResidualChannelGate) : Prop :=
  countertermEmbeddingResidualChannelLedgerDeclared g /\
  g.embeddingResidualCoefficientExplicit /\
  g.embeddingResidualInAllowedBasis /\
  g.embeddingResidualReadyForOneFormDecomposition

theorem embedding_channel_ready_requires_explicit_coefficient
    (g : CountertermEmbeddingResidualChannelGate)
    (hReady : countertermEmbeddingResidualChannelReady g) :
    g.embeddingResidualCoefficientExplicit := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate
end JanusFormal
