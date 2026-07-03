import JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate

set_option autoImplicit false

structure CountertermTetradResidualChannelGate where
  coframeConnectionPullbackGateDeclared : Prop
  residualOneFormDecompositionGateDeclared : Prop
  palatiniHolstTetradVariationBibliographyChecked : Prop
  tetradResidualChannelProblemDeclared : Prop
  coframeVariationBasisDeclared : Prop
  inducedMetricVariationTransportDeclared : Prop
  extrinsicCurvatureVariationTransportDeclared : Prop
  torsionPullbackVariationTransportDeclared : Prop
  z2OrientationVariationPolicyDeclared : Prop
  noFittedTetradResidualCoefficient : Prop
  tetradResidualCoefficientExplicit : Prop
  tetradResidualInAllowedBasis : Prop
  tetradResidualReadyForOneFormDecomposition : Prop

def countertermTetradResidualChannelLedgerDeclared
    (g : CountertermTetradResidualChannelGate) : Prop :=
  g.coframeConnectionPullbackGateDeclared /\
  g.residualOneFormDecompositionGateDeclared /\
  g.palatiniHolstTetradVariationBibliographyChecked /\
  g.tetradResidualChannelProblemDeclared /\
  g.coframeVariationBasisDeclared /\
  g.inducedMetricVariationTransportDeclared /\
  g.extrinsicCurvatureVariationTransportDeclared /\
  g.torsionPullbackVariationTransportDeclared /\
  g.z2OrientationVariationPolicyDeclared /\
  g.noFittedTetradResidualCoefficient

def countertermTetradResidualChannelReady
    (g : CountertermTetradResidualChannelGate) : Prop :=
  countertermTetradResidualChannelLedgerDeclared g /\
  g.tetradResidualCoefficientExplicit /\
  g.tetradResidualInAllowedBasis /\
  g.tetradResidualReadyForOneFormDecomposition

theorem tetrad_channel_ready_requires_explicit_coefficient
    (g : CountertermTetradResidualChannelGate)
    (hReady : countertermTetradResidualChannelReady g) :
    g.tetradResidualCoefficientExplicit := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
end JanusFormal
