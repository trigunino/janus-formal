import JanusFormal.P0EFTJanusZ4FullDerivedSlipCarrierArchiveGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipSurfaceOrthogonalityGate

set_option autoImplicit false

structure DerivedSlipSurfaceOrthogonalityGate where
  surfaceTermParallelFractionRecorded : Prop
  surfaceTermOrthogonalDiagnostic : Prop
  fullDerivedSlipArchived : Prop
  orthogonalResidualBlockedUntilSWClosure : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def surfaceDiagnosticReady (g : DerivedSlipSurfaceOrthogonalityGate) : Prop :=
  g.surfaceTermParallelFractionRecorded /\
  g.surfaceTermOrthogonalDiagnostic /\
  g.fullDerivedSlipArchived /\
  g.orthogonalResidualBlockedUntilSWClosure /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem surface_orthogonality_is_diagnostic_until_sw_closure
    (g : DerivedSlipSurfaceOrthogonalityGate)
    (hPolicy : surfaceDiagnosticReady g -> g.gatePassed)
    (h : surfaceDiagnosticReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipSurfaceOrthogonalityGate
end JanusFormal
