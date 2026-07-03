import JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxTraceRegularityGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGate

set_option autoImplicit false

structure CoupledRadiusFluxSobolevIndexGate where
  traceRegularityGateImported : Prop
  gagliardoTraceBibliographyChecked : Prop
  sobolevMultiplicationBibliographyChecked : Prop
  sigmaDimensionDeclared : Prop
  bulkToBoundaryTraceLossDeclared : Prop
  boundaryAlgebraThresholdDeclared : Prop
  candidateBulkIndexDeclared : Prop
  candidateBoundaryIndexDeclared : Prop
  rSigmaRegularityIndexDeclared : Prop
  tpmTraceRegularityIndexDeclared : Prop
  noIndexFitToObservations : Prop
  candidateIndicesPassTraceThreshold : Prop
  candidateIndicesPassProductThreshold : Prop
  candidateIndicesSupportNormalAndTangentTraces : Prop
  sobolevIndexChoiceReadyForTraceProof : Prop

def sobolevIndexLedgerDeclared
    (g : CoupledRadiusFluxSobolevIndexGate) : Prop :=
  g.traceRegularityGateImported /\
  g.gagliardoTraceBibliographyChecked /\
  g.sobolevMultiplicationBibliographyChecked /\
  g.sigmaDimensionDeclared /\
  g.bulkToBoundaryTraceLossDeclared /\
  g.boundaryAlgebraThresholdDeclared /\
  g.candidateBulkIndexDeclared /\
  g.candidateBoundaryIndexDeclared /\
  g.rSigmaRegularityIndexDeclared /\
  g.tpmTraceRegularityIndexDeclared /\
  g.noIndexFitToObservations

def sobolevIndexReady
    (g : CoupledRadiusFluxSobolevIndexGate) : Prop :=
  sobolevIndexLedgerDeclared g /\
  g.candidateIndicesPassTraceThreshold /\
  g.candidateIndicesPassProductThreshold /\
  g.candidateIndicesSupportNormalAndTangentTraces /\
  g.sobolevIndexChoiceReadyForTraceProof

theorem index_ready_requires_product_threshold
    (g : CoupledRadiusFluxSobolevIndexGate)
    (hReady : sobolevIndexReady g) :
    g.candidateIndicesPassProductThreshold := by
  exact hReady.2.2.1

theorem index_ready_feeds_trace_frontier
    (g : CoupledRadiusFluxSobolevIndexGate)
    (hReady : sobolevIndexReady g) :
    g.sobolevIndexChoiceReadyForTraceProof := by
  exact hReady.2.2.2.2

end P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGate
end JanusFormal
