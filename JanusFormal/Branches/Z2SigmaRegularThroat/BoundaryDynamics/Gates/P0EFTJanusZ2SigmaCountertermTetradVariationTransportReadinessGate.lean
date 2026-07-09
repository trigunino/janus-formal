import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradVariationTransportReadinessGate

set_option autoImplicit false

structure CountertermTetradVariationTransportReadinessGate where
  tetradVariationTransportGateImported : Prop
  metricVariationTransportGateImported : Prop
  extrinsicCurvatureVariationTransportGateImported : Prop
  torsionPullbackVariationTransportGateImported : Prop
  noMetricOnlyShortcut : Prop
  noFittedTetradResidualCoefficient : Prop
  inducedMetricVariationTransportReady : Prop
  extrinsicCurvatureVariationTransportReady : Prop
  torsionPullbackVariationTransportReady : Prop
  tetradVariationTransportReady : Prop

def tetradVariationReadinessLedgerDeclared
    (g : CountertermTetradVariationTransportReadinessGate) : Prop :=
  g.tetradVariationTransportGateImported /\
  g.metricVariationTransportGateImported /\
  g.extrinsicCurvatureVariationTransportGateImported /\
  g.torsionPullbackVariationTransportGateImported /\
  g.noMetricOnlyShortcut /\
  g.noFittedTetradResidualCoefficient

def tetradVariationReadinessReady
    (g : CountertermTetradVariationTransportReadinessGate) : Prop :=
  tetradVariationReadinessLedgerDeclared g /\
  g.inducedMetricVariationTransportReady /\
  g.extrinsicCurvatureVariationTransportReady /\
  g.torsionPullbackVariationTransportReady /\
  g.tetradVariationTransportReady

theorem tetrad_readiness_requires_deltaK
    (g : CountertermTetradVariationTransportReadinessGate)
    (hReady : tetradVariationReadinessReady g) :
    g.extrinsicCurvatureVariationTransportReady := by
  exact hReady.2.2.1

theorem tetrad_readiness_feeds_parent_transport
    (g : CountertermTetradVariationTransportReadinessGate)
    (hReady : tetradVariationReadinessReady g) :
    g.tetradVariationTransportReady := by
  exact hReady.2.2.2.2

theorem missing_deltaK_transport_blocks_tetrad_readiness
    (g : CountertermTetradVariationTransportReadinessGate)
    (hMissing : Not g.extrinsicCurvatureVariationTransportReady) :
    Not (tetradVariationReadinessReady g) := by
  intro hReady
  exact hMissing (tetrad_readiness_requires_deltaK g hReady)

end P0EFTJanusZ2SigmaCountertermTetradVariationTransportReadinessGate
end JanusFormal
