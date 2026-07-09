import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MinusSectorDecouplingLawGate

namespace JanusFormal
namespace P0EFTJanusZ4UniqueEquationMasterGate

set_option autoImplicit false

structure UniqueEquationMasterGate where
  frozenPatchworkBranchesAcknowledged : Prop
  masterVariableDeclared : Prop
  masterOperatorDeclared : Prop
  masterSourceDeclared : Prop
  z4ParityDeclared : Prop
  boundaryOrOrbifoldConditionsDeclared : Prop
  grLimitDeclared : Prop
  plusMinusReconstructionDeclared : Prop
  observableProjectionDeclared : Prop
  masterEquationSolved : Prop
  masterSolutionAvailable : Prop
  independentDeltaSlipAllowed : Prop
  independentDopplerAllowed : Prop
  independentPiAllowed : Prop
  independentMinusSectorAmplitudeAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def masterGateReady (g : UniqueEquationMasterGate) : Prop :=
  g.frozenPatchworkBranchesAcknowledged /\
  g.masterVariableDeclared /\
  g.masterOperatorDeclared /\
  g.masterSourceDeclared /\
  g.z4ParityDeclared /\
  g.boundaryOrOrbifoldConditionsDeclared /\
  g.grLimitDeclared /\
  g.plusMinusReconstructionDeclared /\
  g.observableProjectionDeclared /\
  Not g.masterEquationSolved /\
  Not g.masterSolutionAvailable /\
  Not g.independentDeltaSlipAllowed /\
  Not g.independentDopplerAllowed /\
  Not g.independentPiAllowed /\
  Not g.independentMinusSectorAmplitudeAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem unique_master_gate_blocks_downstream_patches
    (g : UniqueEquationMasterGate)
    (hPolicy : masterGateReady g -> g.gatePassed)
    (h : masterGateReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4UniqueEquationMasterGate
end JanusFormal
