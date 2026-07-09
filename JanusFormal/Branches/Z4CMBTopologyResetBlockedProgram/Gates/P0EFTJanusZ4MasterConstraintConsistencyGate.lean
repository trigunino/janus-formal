import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterReconstructionGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterConstraintConsistencyGate

set_option autoImplicit false

structure MasterConstraintConsistencyGate where
  masterReconstructionGatePassed : Prop
  constraintChecksDeclared : Prop
  bianchiConsistencyRequired : Prop
  plusMinusConservationRequired : Prop
  traceFreeSlipConsistencyRequired : Prop
  dopplerContinuityConsistencyRequired : Prop
  piFromMultipolesRequired : Prop
  projectionZ4CompatibilityRequired : Prop
  grLimitRequired : Prop
  allConstraintsPassed : Prop
  blockedUntilMasterReconstruction : Prop
  independentDownstreamSourceAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def consistencyGateReady (g : MasterConstraintConsistencyGate) : Prop :=
  g.masterReconstructionGatePassed /\
  g.constraintChecksDeclared /\
  g.bianchiConsistencyRequired /\
  g.plusMinusConservationRequired /\
  g.traceFreeSlipConsistencyRequired /\
  g.dopplerContinuityConsistencyRequired /\
  g.piFromMultipolesRequired /\
  g.projectionZ4CompatibilityRequired /\
  g.grLimitRequired /\
  Not g.allConstraintsPassed /\
  g.blockedUntilMasterReconstruction /\
  Not g.independentDownstreamSourceAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem master_constraint_gate_blocks_until_reconstruction
    (g : MasterConstraintConsistencyGate)
    (hPolicy : consistencyGateReady g -> g.gatePassed)
    (h : consistencyGateReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterConstraintConsistencyGate
end JanusFormal
