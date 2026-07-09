import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4NonOverlappingLikelihoodAccountingGate

namespace JanusFormal
namespace P0EFTJanusZ4HighLDecomposedCandidatePromotionGate

set_option autoImplicit false

structure HighLDecomposedCandidatePromotionGate where
  grHandshakeTEEEPassed : Prop
  frozenCandidateInvariant : Prop
  noRetuning : Prop
  combinedHighlTotalImproves : Prop
  decomposedHighlTotalImproves : Prop
  teStandaloneCostSmall : Prop
  eeStandaloneNotDegraded : Prop
  transportGuardsPass : Prop
  fullPlanckValidation : Prop
  promoted : Prop

def promotionReady (g : HighLDecomposedCandidatePromotionGate) : Prop :=
  g.grHandshakeTEEEPassed /\
  g.frozenCandidateInvariant /\
  g.noRetuning /\
  g.combinedHighlTotalImproves /\
  g.decomposedHighlTotalImproves /\
  g.teStandaloneCostSmall /\
  g.eeStandaloneNotDegraded /\
  g.transportGuardsPass /\
  Not g.fullPlanckValidation

theorem promotion_ready_promotes_candidate
    (g : HighLDecomposedCandidatePromotionGate)
    (hPolicy : promotionReady g -> g.promoted)
    (h : promotionReady g) :
    g.promoted := by
  exact hPolicy h

end P0EFTJanusZ4HighLDecomposedCandidatePromotionGate
end JanusFormal
