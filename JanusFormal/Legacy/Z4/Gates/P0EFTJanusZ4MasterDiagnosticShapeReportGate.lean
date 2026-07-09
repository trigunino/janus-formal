import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterDiagnosticSpectraGenerationGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterDiagnosticShapeReportGate

set_option autoImplicit false

structure MasterDiagnosticShapeReportGate where
  diagnosticSpectraGenerationGatePassed : Prop
  shapeReportGenerated : Prop
  channelRatioStatsReported : Prop
  peakShiftStatsReported : Prop
  zeroCountStatsReported : Prop
  phaseGuardReported : Prop
  amplitudeGuardReported : Prop
  diagnosticOnly : Prop
  likelihoodEvaluationAllowed : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def shapeReportReady (g : MasterDiagnosticShapeReportGate) : Prop :=
  g.diagnosticSpectraGenerationGatePassed /\
  g.shapeReportGenerated /\
  g.channelRatioStatsReported /\
  g.peakShiftStatsReported /\
  g.zeroCountStatsReported /\
  g.phaseGuardReported /\
  g.amplitudeGuardReported /\
  g.diagnosticOnly /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem shape_report_is_diagnostic_only
    (g : MasterDiagnosticShapeReportGate)
    (hPolicy : shapeReportReady g -> g.gatePassed)
    (h : shapeReportReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterDiagnosticShapeReportGate
end JanusFormal
