import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ClosedBoltzmannCandidateHighLDecompositionTrial

namespace JanusFormal
namespace P0EFTJanusZ4NonOverlappingLikelihoodAccountingGate

set_option autoImplicit false

structure NonOverlappingAccountingGate where
  combinedHighlTotalDefined : Prop
  decomposedHighlTotalDefined : Prop
  overlappingHighlSumForbidden : Prop
  reportedTotalUsesOneHighlBasisOnly : Prop
  legacyOverlappingTotalDiagnosticOnly : Prop
  nonoverlappingCombinedImproves : Prop
  nonoverlappingDecomposedImproves : Prop
  teStandaloneCostSmall : Prop
  eeStandaloneNotDegraded : Prop
  gatePassed : Prop

def accountingReady (g : NonOverlappingAccountingGate) : Prop :=
  g.combinedHighlTotalDefined /\
  g.decomposedHighlTotalDefined /\
  g.overlappingHighlSumForbidden /\
  g.reportedTotalUsesOneHighlBasisOnly /\
  g.legacyOverlappingTotalDiagnosticOnly /\
  g.nonoverlappingCombinedImproves /\
  g.nonoverlappingDecomposedImproves /\
  g.teStandaloneCostSmall /\
  g.eeStandaloneNotDegraded

theorem accounting_ready_passes_gate
    (g : NonOverlappingAccountingGate)
    (hPolicy : accountingReady g -> g.gatePassed)
    (h : accountingReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4NonOverlappingLikelihoodAccountingGate
end JanusFormal
