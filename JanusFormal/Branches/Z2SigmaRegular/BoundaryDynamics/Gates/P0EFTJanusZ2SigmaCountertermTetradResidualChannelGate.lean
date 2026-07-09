import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate

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
  tetradMetricResidualSubchannelExplicit : Prop
  tetradMetricResidualCoefficientFormulaDeclared : Prop
  tetradMetricResidualCoefficientValueReady : Prop
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
  g.tetradMetricResidualCoefficientFormulaDeclared /\
  g.tetradMetricResidualCoefficientValueReady /\
  g.tetradResidualCoefficientExplicit /\
  g.tetradResidualInAllowedBasis /\
  g.tetradResidualReadyForOneFormDecomposition

theorem tetrad_channel_ready_requires_explicit_coefficient
    (g : CountertermTetradResidualChannelGate)
    (hReady : countertermTetradResidualChannelReady g) :
    g.tetradResidualCoefficientExplicit := by
  exact hReady.right.right.right.left

theorem metric_subchannel_alone_does_not_close_tetrad_channel
    (g : CountertermTetradResidualChannelGate)
    (_hMetricOnly : g.tetradMetricResidualSubchannelExplicit)
    (hMissing : Not g.tetradResidualCoefficientExplicit) :
    Not (countertermTetradResidualChannelReady g) := by
  intro hReady
  exact hMissing (tetrad_channel_ready_requires_explicit_coefficient g hReady)

theorem metric_coefficient_formula_without_value_does_not_close_tetrad_channel
    (g : CountertermTetradResidualChannelGate)
    (_hFormula : g.tetradMetricResidualCoefficientFormulaDeclared)
    (hNoValue : Not g.tetradMetricResidualCoefficientValueReady) :
    Not (g.tetradMetricResidualCoefficientFormulaDeclared /\
      countertermTetradResidualChannelReady g) := by
  intro h
  exact hNoValue h.2.right.right.left

end P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
end JanusFormal
