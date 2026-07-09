import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeylLateISWConsistencyGate

namespace JanusFormal
namespace P0EFTJanusZ4OfficialPlanckWeylLateISWDeltaTrial

set_option autoImplicit false

structure OfficialPlanckWeylLateISWDeltaTrial where
  consistencyGatePassed : Prop
  cambGRPlusZ4DeltaBackend : Prop
  sharedWeylLensingEnabled : Prop
  lateISWSourceEnabled : Prop
  earlyISWEnabled : Prop
  acousticDeltaEnabled : Prop
  recombinationDeltaEnabled : Prop
  polarizationDeltaEnabled : Prop
  nativeToyLOSUsed : Prop
  fullNativeZ4SolverUsed : Prop
  officialLikelihoodExecuted : Prop
  planckSuccessVerdict : Prop

def controlledWeylLateISWTrialReady (t : OfficialPlanckWeylLateISWDeltaTrial) : Prop :=
  t.consistencyGatePassed /\
  t.cambGRPlusZ4DeltaBackend /\
  t.sharedWeylLensingEnabled /\
  t.lateISWSourceEnabled /\
  Not t.earlyISWEnabled /\
  Not t.acousticDeltaEnabled /\
  Not t.recombinationDeltaEnabled /\
  Not t.polarizationDeltaEnabled /\
  Not t.nativeToyLOSUsed /\
  Not t.fullNativeZ4SolverUsed

theorem ready_trial_can_execute_likelihood
    (t : OfficialPlanckWeylLateISWDeltaTrial)
    (hPolicy : controlledWeylLateISWTrialReady t -> t.officialLikelihoodExecuted)
    (h : controlledWeylLateISWTrialReady t) :
    t.officialLikelihoodExecuted := by
  exact hPolicy h

theorem executed_trial_is_not_success_verdict
    (t : OfficialPlanckWeylLateISWDeltaTrial)
    (hNoVerdict : Not t.planckSuccessVerdict) :
    Not t.planckSuccessVerdict := by
  exact hNoVerdict

end P0EFTJanusZ4OfficialPlanckWeylLateISWDeltaTrial
end JanusFormal
