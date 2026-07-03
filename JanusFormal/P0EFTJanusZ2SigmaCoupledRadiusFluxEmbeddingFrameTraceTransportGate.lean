import JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGate

set_option autoImplicit false

structure CoupledRadiusFluxEmbeddingFrameTraceTransportGate where
  normalTangentTraceSupportGateImported : Prop
  embeddingRegularityEquivarianceImported : Prop
  hypersurfaceFrameTheoremImported : Prop
  regularEmbeddingReady : Prop
  coorientationReady : Prop
  inducedMetricNondegenerateReady : Prop
  frameTraceTransportDeclared : Prop
  noIndependentFrameFit : Prop
  tangentFrameTraceSupported : Prop
  normalTraceSupported : Prop
  tangentFrameTraceContinuous : Prop
  normalTraceContinuous : Prop
  candidateIndicesSupportNormalAndTangentTraces : Prop

def embeddingFrameTraceTransportLedgerDeclared
    (g : CoupledRadiusFluxEmbeddingFrameTraceTransportGate) : Prop :=
  g.normalTangentTraceSupportGateImported /\
  g.embeddingRegularityEquivarianceImported /\
  g.hypersurfaceFrameTheoremImported /\
  g.frameTraceTransportDeclared /\
  g.noIndependentFrameFit

def embeddingFrameTraceTransportReady
    (g : CoupledRadiusFluxEmbeddingFrameTraceTransportGate) : Prop :=
  embeddingFrameTraceTransportLedgerDeclared g /\
  g.regularEmbeddingReady /\
  g.coorientationReady /\
  g.inducedMetricNondegenerateReady /\
  g.tangentFrameTraceSupported /\
  g.normalTraceSupported /\
  g.tangentFrameTraceContinuous /\
  g.normalTraceContinuous /\
  g.candidateIndicesSupportNormalAndTangentTraces

theorem frame_trace_transport_requires_embedding
    (g : CoupledRadiusFluxEmbeddingFrameTraceTransportGate)
    (hReady : embeddingFrameTraceTransportReady g) :
    g.regularEmbeddingReady := by
  exact hReady.2.1

theorem frame_trace_transport_feeds_normal_tangent_support
    (g : CoupledRadiusFluxEmbeddingFrameTraceTransportGate)
    (hReady : embeddingFrameTraceTransportReady g) :
    g.candidateIndicesSupportNormalAndTangentTraces := by
  exact hReady.2.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGate
end JanusFormal
