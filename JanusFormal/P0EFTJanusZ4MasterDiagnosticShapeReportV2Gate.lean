import JanusFormal.P0EFTJanusZ4MasterRegularizedDiagnosticSpectraV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterDiagnosticShapeReportV2Gate

set_option autoImplicit false

structure MasterDiagnosticShapeReportV2Gate where
  diagnosticSpectraV2GatePassed : Prop
  shapeReportV2Generated : Prop
  phaseGuardPassed : Prop
  amplitudeGuardPassed : Prop
  zeroArtifactGuardPassed : Prop
  nonoverlapAccountingBasisDeclared : Prop
  overlappingSumForbidden : Prop
  reportedTotalUsesOneHighLBasisOnly : Prop
  diagnosticOnly : Prop
  likelihoodEvaluationAllowed : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def shapeReportV2Ready (g : MasterDiagnosticShapeReportV2Gate) : Prop :=
  g.diagnosticSpectraV2GatePassed /\
  g.shapeReportV2Generated /\
  g.phaseGuardPassed /\
  g.amplitudeGuardPassed /\
  g.zeroArtifactGuardPassed /\
  g.nonoverlapAccountingBasisDeclared /\
  g.overlappingSumForbidden /\
  g.reportedTotalUsesOneHighLBasisOnly /\
  g.diagnosticOnly /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem shape_report_v2_blocks_overlap_and_likelihood
    (g : MasterDiagnosticShapeReportV2Gate)
    (hPolicy : shapeReportV2Ready g -> g.gatePassed)
    (h : shapeReportV2Ready g) :
    g.gatePassed /\ Not g.likelihoodEvaluationAllowed /\ Not g.candidatePromotionAllowed := by
  have hGate : g.gatePassed := hPolicy h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hNoLike, _, hNoPromotion, _, _⟩
  exact ⟨hGate, hNoLike, hNoPromotion⟩

end P0EFTJanusZ4MasterDiagnosticShapeReportV2Gate
end JanusFormal
