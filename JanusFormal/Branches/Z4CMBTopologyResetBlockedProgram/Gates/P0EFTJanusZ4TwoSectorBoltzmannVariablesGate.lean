import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeakSurfaceBranchDiagnosticClosureGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorBoltzmannVariablesGate

set_option autoImplicit false

structure TwoSectorBoltzmannVariablesGate where
  previousSlipSurfaceBranchesArchived : Prop
  plusSectorDeclared : Prop
  minusSectorDeclared : Prop
  metricPlusMinusDeclared : Prop
  z4ProjectionDeclared : Prop
  couplingMatrixDeclared : Prop
  signConventionDeclared : Prop
  rhoEffShortcutForbidden : Prop
  directClPatchForbidden : Prop
  rawToyLOSForbidden : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  carrierTangentProjectionRequiredBeforePromotion : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def variablesReady (g : TwoSectorBoltzmannVariablesGate) : Prop :=
  g.previousSlipSurfaceBranchesArchived /\
  g.plusSectorDeclared /\
  g.minusSectorDeclared /\
  g.metricPlusMinusDeclared /\
  g.z4ProjectionDeclared /\
  g.couplingMatrixDeclared /\
  g.signConventionDeclared /\
  g.rhoEffShortcutForbidden /\
  g.directClPatchForbidden /\
  g.rawToyLOSForbidden /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  g.carrierTangentProjectionRequiredBeforePromotion /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem two_sector_variables_gate_blocks_shortcuts
    (g : TwoSectorBoltzmannVariablesGate)
    (hPolicy : variablesReady g -> g.gatePassed)
    (h : variablesReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorBoltzmannVariablesGate
end JanusFormal
