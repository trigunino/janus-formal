import JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGate
import JanusFormal.P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGate

set_option autoImplicit false

structure CoupledRadiusFluxNormalTangentTraceSupportGate where
  thresholdTransportGateImported : Prop
  embeddingRegularityGateImported : Prop
  hypersurfaceGeometryBibliographyChecked : Prop
  regularEmbeddingAssumptionDeclared : Prop
  coorientationDeclared : Prop
  tangentFrameFromEmbeddingDeclared : Prop
  unitNormalFromEmbeddingDeclared : Prop
  metricNondegeneracyDeclared : Prop
  noIndependentFrameFit : Prop
  tangentFrameTraceSupported : Prop
  normalTraceSupported : Prop
  tangentFrameTraceContinuous : Prop
  normalTraceContinuous : Prop
  candidateIndicesSupportNormalAndTangentTraces : Prop

def normalTangentTraceLedgerDeclared
    (g : CoupledRadiusFluxNormalTangentTraceSupportGate) : Prop :=
  g.thresholdTransportGateImported /\
  g.embeddingRegularityGateImported /\
  g.hypersurfaceGeometryBibliographyChecked /\
  g.regularEmbeddingAssumptionDeclared /\
  g.coorientationDeclared /\
  g.tangentFrameFromEmbeddingDeclared /\
  g.unitNormalFromEmbeddingDeclared /\
  g.metricNondegeneracyDeclared /\
  g.noIndependentFrameFit

def normalTangentTraceSupportReady
    (g : CoupledRadiusFluxNormalTangentTraceSupportGate) : Prop :=
  normalTangentTraceLedgerDeclared g /\
  g.tangentFrameTraceSupported /\
  g.normalTraceSupported /\
  g.tangentFrameTraceContinuous /\
  g.normalTraceContinuous /\
  g.candidateIndicesSupportNormalAndTangentTraces

theorem normal_tangent_ready_requires_regular_embedding
    (g : CoupledRadiusFluxNormalTangentTraceSupportGate)
    (hReady : normalTangentTraceSupportReady g) :
    g.regularEmbeddingAssumptionDeclared := by
  exact hReady.1.2.2.2.1

theorem normal_tangent_ready_feeds_sobolev_index_frontier
    (g : CoupledRadiusFluxNormalTangentTraceSupportGate)
    (hReady : normalTangentTraceSupportReady g) :
    g.candidateIndicesSupportNormalAndTangentTraces := by
  exact hReady.2.2.2.2.2

end P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGate
end JanusFormal
