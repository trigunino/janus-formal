import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate

set_option autoImplicit false

structure CountertermConnectionResidualChannelGate where
  coframeConnectionPullbackGateDeclared : Prop
  torsionPullbackOnSigmaGateDeclared : Prop
  holstNiehYanRadialBlockGateDeclared : Prop
  connectionVariationTransportGateDeclared : Prop
  palatiniHolstConnectionVariationBibliographyChecked : Prop
  spinConnectionVariationBasisDeclared : Prop
  connectionResidualChannelProblemDeclared : Prop
  torsionVariationTransportDeclared : Prop
  niehYanBoundaryVariationTransportDeclared : Prop
  z2OrientationVariationPolicyDeclared : Prop
  noFittedConnectionResidualCoefficient : Prop
  fixedEmbeddingCommutationSubchannelReady : Prop
  connectionVariationTransportReady : Prop
  connectionResidualCoefficientExplicit : Prop
  connectionResidualInAllowedBasis : Prop
  connectionResidualReadyForOneFormDecomposition : Prop

def countertermConnectionResidualChannelLedgerDeclared
    (g : CountertermConnectionResidualChannelGate) : Prop :=
  g.coframeConnectionPullbackGateDeclared /\
  g.torsionPullbackOnSigmaGateDeclared /\
  g.holstNiehYanRadialBlockGateDeclared /\
  g.connectionVariationTransportGateDeclared /\
  g.palatiniHolstConnectionVariationBibliographyChecked /\
  g.spinConnectionVariationBasisDeclared /\
  g.connectionResidualChannelProblemDeclared /\
  g.torsionVariationTransportDeclared /\
  g.niehYanBoundaryVariationTransportDeclared /\
  g.z2OrientationVariationPolicyDeclared /\
  g.noFittedConnectionResidualCoefficient

def countertermConnectionResidualChannelReady
    (g : CountertermConnectionResidualChannelGate) : Prop :=
  countertermConnectionResidualChannelLedgerDeclared g /\
  g.fixedEmbeddingCommutationSubchannelReady /\
  g.connectionVariationTransportReady /\
  g.connectionResidualCoefficientExplicit /\
  g.connectionResidualInAllowedBasis /\
  g.connectionResidualReadyForOneFormDecomposition

theorem connection_channel_ready_requires_explicit_coefficient
    (g : CountertermConnectionResidualChannelGate)
    (hReady : countertermConnectionResidualChannelReady g) :
    g.connectionResidualCoefficientExplicit := by
  exact hReady.right.right.right.left

theorem fixed_embedding_commutation_alone_does_not_close_connection_channel
    (g : CountertermConnectionResidualChannelGate)
    (hNoTransport : ¬ g.connectionVariationTransportReady) :
    ¬ (g.fixedEmbeddingCommutationSubchannelReady /\
      countertermConnectionResidualChannelReady g) := by
  intro h
  exact hNoTransport h.2.2.2.1

end P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate
end JanusFormal
