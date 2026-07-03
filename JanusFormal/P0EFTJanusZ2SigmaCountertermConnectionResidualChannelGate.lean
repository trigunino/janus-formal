import JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
import JanusFormal.P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate

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
  g.connectionResidualCoefficientExplicit /\
  g.connectionResidualInAllowedBasis /\
  g.connectionResidualReadyForOneFormDecomposition

theorem connection_channel_ready_requires_explicit_coefficient
    (g : CountertermConnectionResidualChannelGate)
    (hReady : countertermConnectionResidualChannelReady g) :
    g.connectionResidualCoefficientExplicit := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate
end JanusFormal
