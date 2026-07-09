import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4AcousticDrivingDeltaGate

namespace JanusFormal
namespace P0EFTJanusZ4OfficialPlanckAcousticDrivingDeltaTrial

set_option autoImplicit false

structure OfficialPlanckAcousticDrivingDeltaTrial where
  acousticGatePassed : Prop
  effectiveAcousticTemperatureSourceDelta : Prop
  surfaceOnlyTrial : Prop
  earlyISWOnlyTrial : Prop
  fullSourceTrial : Prop
  metricSplitUsed : Prop
  deltaSlipZeroUntilDerived : Prop
  polarizationSourceDeltaEnabled : Prop
  eeExpectedUnchanged : Prop
  lensingDeltaEnabled : Prop
  cPhiPhiExpectedUnchanged : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  primordialDeltaEnabled : Prop
  nativeToyLOSUsed : Prop
  fullNativeZ4SolverUsed : Prop
  officialLikelihoodExecuted : Prop
  planckSuccessVerdict : Prop
  fullZ4Verdict : Prop

def controlledAcousticTrialReady (t : OfficialPlanckAcousticDrivingDeltaTrial) : Prop :=
  t.acousticGatePassed /\
  t.effectiveAcousticTemperatureSourceDelta /\
  t.surfaceOnlyTrial /\
  t.earlyISWOnlyTrial /\
  t.fullSourceTrial /\
  t.metricSplitUsed /\
  t.deltaSlipZeroUntilDerived /\
  Not t.polarizationSourceDeltaEnabled /\
  t.eeExpectedUnchanged /\
  Not t.lensingDeltaEnabled /\
  t.cPhiPhiExpectedUnchanged /\
  Not t.recombinationDeltaEnabled /\
  Not t.visibilityDeltaEnabled /\
  Not t.backgroundProjectionChanged /\
  Not t.primordialDeltaEnabled /\
  Not t.nativeToyLOSUsed /\
  Not t.fullNativeZ4SolverUsed

theorem ready_trial_can_execute_likelihood
    (t : OfficialPlanckAcousticDrivingDeltaTrial)
    (hPolicy : controlledAcousticTrialReady t -> t.officialLikelihoodExecuted)
    (h : controlledAcousticTrialReady t) :
    t.officialLikelihoodExecuted := by
  exact hPolicy h

theorem controlled_trial_is_not_full_verdict
    (t : OfficialPlanckAcousticDrivingDeltaTrial)
    (hNoSuccess : t.officialLikelihoodExecuted -> Not t.planckSuccessVerdict)
    (hNoFull : t.officialLikelihoodExecuted -> Not t.fullZ4Verdict)
    (h : t.officialLikelihoodExecuted) :
    Not t.planckSuccessVerdict /\ Not t.fullZ4Verdict := by
  exact And.intro (hNoSuccess h) (hNoFull h)

end P0EFTJanusZ4OfficialPlanckAcousticDrivingDeltaTrial
end JanusFormal
