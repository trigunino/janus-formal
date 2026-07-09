import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGate

set_option autoImplicit false

structure CoupledRadiusFluxSobolevThresholdTransportGate where
  sobolevIndexGateImported : Prop
  gagliardoTraceTheoremAvailable : Prop
  sobolevAlgebraTheoremAvailable : Prop
  sigmaDimensionThreeUsed : Prop
  traceLossOneHalfUsed : Prop
  candidateBulkIndexAtLeastThree : Prop
  candidateBoundaryIndexAtLeastFiveHalves : Prop
  boundaryIndexAboveThreeHalves : Prop
  noRegularityFitToObservations : Prop
  candidateIndicesPassTraceThreshold : Prop
  candidateIndicesPassProductThreshold : Prop
  normalAndTangentFrameSupportStillOpen : Prop

def thresholdTransportLedgerDeclared
    (g : CoupledRadiusFluxSobolevThresholdTransportGate) : Prop :=
  g.sobolevIndexGateImported /\
  g.gagliardoTraceTheoremAvailable /\
  g.sobolevAlgebraTheoremAvailable /\
  g.sigmaDimensionThreeUsed /\
  g.traceLossOneHalfUsed /\
  g.candidateBulkIndexAtLeastThree /\
  g.candidateBoundaryIndexAtLeastFiveHalves /\
  g.boundaryIndexAboveThreeHalves /\
  g.noRegularityFitToObservations

def traceAndProductThresholdsTransported
    (g : CoupledRadiusFluxSobolevThresholdTransportGate) : Prop :=
  thresholdTransportLedgerDeclared g /\
  g.candidateIndicesPassTraceThreshold /\
  g.candidateIndicesPassProductThreshold /\
  g.normalAndTangentFrameSupportStillOpen

theorem transported_thresholds_give_trace_threshold
    (g : CoupledRadiusFluxSobolevThresholdTransportGate)
    (hReady : traceAndProductThresholdsTransported g) :
    g.candidateIndicesPassTraceThreshold := by
  exact hReady.2.1

theorem transported_thresholds_give_product_threshold
    (g : CoupledRadiusFluxSobolevThresholdTransportGate)
    (hReady : traceAndProductThresholdsTransported g) :
    g.candidateIndicesPassProductThreshold := by
  exact hReady.2.2.1

end P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGate
end JanusFormal
