import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterSourceCarrierTangentReplayGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterDiagnosticSpectraReadinessGate

set_option autoImplicit false

structure MasterDiagnosticSpectraReadinessGate where
  masterSourceCarrierTangentReplayPassed : Prop
  sourcePassesCarrierThreshold : Prop
  constraintClosureAuditPassed : Prop
  allSourcesFromSameUZ4 : Prop
  diagnosticSpectraGenerationAllowed : Prop
  officialPlanckTrialAllowed : Prop
  likelihoodEvaluationAllowed : Prop
  candidatePromotionAllowed : Prop
  lambdaRetuningAllowed : Prop
  nuisanceRefitAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def readinessGateReady (g : MasterDiagnosticSpectraReadinessGate) : Prop :=
  g.masterSourceCarrierTangentReplayPassed /\
  g.sourcePassesCarrierThreshold /\
  g.constraintClosureAuditPassed /\
  g.allSourcesFromSameUZ4 /\
  g.diagnosticSpectraGenerationAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.lambdaRetuningAllowed /\
  Not g.nuisanceRefitAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem diagnostic_spectra_readiness_is_not_planck_validation
    (g : MasterDiagnosticSpectraReadinessGate)
    (hPolicy : readinessGateReady g -> g.gatePassed)
    (h : readinessGateReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterDiagnosticSpectraReadinessGate
end JanusFormal
