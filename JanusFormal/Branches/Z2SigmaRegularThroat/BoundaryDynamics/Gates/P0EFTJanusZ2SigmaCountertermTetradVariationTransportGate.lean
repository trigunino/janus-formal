import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate

set_option autoImplicit false

structure CountertermTetradVariationTransportGate where
  tetradResidualChannelImported : Prop
  extrinsicCurvatureGateImported : Prop
  torsionPullbackGateImported : Prop
  palatiniHolstTetradVariationBibliographyChecked : Prop
  coframeVariationBasisDeclared : Prop
  deltaEToDeltaHDeclared : Prop
  deltaEToDeltaKDeclared : Prop
  deltaEToDeltaTorsionPullbackDeclared : Prop
  z2OrientationVariationPolicyDeclared : Prop
  noMetricOnlyShortcut : Prop
  noFittedTetradResidualCoefficient : Prop
  inducedMetricVariationTransportReady : Prop
  extrinsicCurvatureVariationTransportReady : Prop
  torsionPullbackVariationTransportReady : Prop
  tetradVariationTransportReady : Prop

def tetradVariationTransportLedgerDeclared
    (g : CountertermTetradVariationTransportGate) : Prop :=
  g.tetradResidualChannelImported /\
  g.extrinsicCurvatureGateImported /\
  g.torsionPullbackGateImported /\
  g.palatiniHolstTetradVariationBibliographyChecked /\
  g.coframeVariationBasisDeclared /\
  g.deltaEToDeltaHDeclared /\
  g.deltaEToDeltaKDeclared /\
  g.deltaEToDeltaTorsionPullbackDeclared /\
  g.z2OrientationVariationPolicyDeclared /\
  g.noMetricOnlyShortcut /\
  g.noFittedTetradResidualCoefficient

def tetradVariationTransportReady
    (g : CountertermTetradVariationTransportGate) : Prop :=
  tetradVariationTransportLedgerDeclared g /\
  g.inducedMetricVariationTransportReady /\
  g.extrinsicCurvatureVariationTransportReady /\
  g.torsionPullbackVariationTransportReady /\
  g.tetradVariationTransportReady

theorem tetrad_transport_requires_deltaK_transport
    (g : CountertermTetradVariationTransportGate)
    (hReady : tetradVariationTransportReady g) :
    g.extrinsicCurvatureVariationTransportReady := by
  exact hReady.2.2.1

theorem tetrad_transport_feeds_tetrad_residual_channel
    (g : CountertermTetradVariationTransportGate)
    (hReady : tetradVariationTransportReady g) :
    g.tetradVariationTransportReady := by
  exact hReady.2.2.2.2

end P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate
end JanusFormal
