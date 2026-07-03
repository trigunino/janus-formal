import JanusFormal.P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate
import JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGate

set_option autoImplicit false

structure CountertermTetradExtrinsicCurvatureVariationTransportGate where
  tetradVariationTransportGateImported : Prop
  extrinsicCurvatureGateImported : Prop
  coupledRadiusFluxEmbeddingFrameTraceTransportGateImported : Prop
  hypersurfaceVariationBibliographyChecked : Prop
  kAbFormulaDeclared : Prop
  deltaKFormulaDeclared : Prop
  deltaEToDeltaTangentFrameDeclared : Prop
  deltaEToDeltaNormalDeclared : Prop
  deltaEToDeltaConnectionDeclared : Prop
  z2NormalOrientationVariationDeclared : Prop
  noFittedExtrinsicCurvatureVariation : Prop
  activeEmbeddingReady : Prop
  tangentNormalTraceTransportReady : Prop
  connectionVariationTransportReady : Prop
  deltaKInAllowedBasis : Prop
  extrinsicCurvatureVariationTransportReady : Prop

def extrinsicCurvatureVariationTransportLedgerDeclared
    (g : CountertermTetradExtrinsicCurvatureVariationTransportGate) : Prop :=
  g.tetradVariationTransportGateImported /\
  g.extrinsicCurvatureGateImported /\
  g.coupledRadiusFluxEmbeddingFrameTraceTransportGateImported /\
  g.hypersurfaceVariationBibliographyChecked /\
  g.kAbFormulaDeclared /\
  g.deltaKFormulaDeclared /\
  g.deltaEToDeltaTangentFrameDeclared /\
  g.deltaEToDeltaNormalDeclared /\
  g.deltaEToDeltaConnectionDeclared /\
  g.z2NormalOrientationVariationDeclared /\
  g.noFittedExtrinsicCurvatureVariation

def extrinsicCurvatureVariationTransportReady
    (g : CountertermTetradExtrinsicCurvatureVariationTransportGate) : Prop :=
  extrinsicCurvatureVariationTransportLedgerDeclared g /\
  g.activeEmbeddingReady /\
  g.tangentNormalTraceTransportReady /\
  g.connectionVariationTransportReady /\
  g.deltaKInAllowedBasis /\
  g.extrinsicCurvatureVariationTransportReady

theorem deltaK_transport_requires_embedding
    (g : CountertermTetradExtrinsicCurvatureVariationTransportGate)
    (hReady : extrinsicCurvatureVariationTransportReady g) :
    g.activeEmbeddingReady := by
  exact hReady.2.1

theorem deltaK_transport_feeds_tetrad_transport
    (g : CountertermTetradExtrinsicCurvatureVariationTransportGate)
    (hReady : extrinsicCurvatureVariationTransportReady g) :
    g.extrinsicCurvatureVariationTransportReady := by
  exact hReady.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGate
end JanusFormal
