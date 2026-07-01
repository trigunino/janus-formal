import JanusFormal.P0EFTJanusZ4MetricPotentialSplitGate

namespace JanusFormal
namespace P0EFTJanusZ4AcousticDrivingDeltaGate

set_option autoImplicit false

structure AcousticDrivingDeltaGate where
  metricPotentialSplitGatePassed : Prop
  metricSplitUsed : Prop
  deltaSlipZeroUntilDerived : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  soundHorizonChanged : Prop
  dragHorizonChanged : Prop
  primordialDeltaEnabled : Prop
  polarizationSourceDeltaEnabled : Prop
  earlyAcousticWindowEnabled : Prop
  earlyISWDeltaEnabled : Prop
  lateISWLeakage : Prop
  eeUnlensedUnchanged : Prop
  cPhiPhiUnchanged : Prop
  ttUnlensedMayChange : Prop
  teUnlensedMayChange : Prop
  lambdaZeroIdentityPassed : Prop
  smallLambdaContinuityPassed : Prop
  acousticDrivingDeltaGatePassed : Prop
  officialPlanckAcousticDrivingTrialAllowed : Prop
  fullNativeZ4Verdict : Prop

def acousticDrivingReady (g : AcousticDrivingDeltaGate) : Prop :=
  g.metricPotentialSplitGatePassed /\
  g.metricSplitUsed /\
  g.deltaSlipZeroUntilDerived /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.recombinationDeltaEnabled /\
  Not g.visibilityDeltaEnabled /\
  Not g.backgroundProjectionChanged /\
  Not g.soundHorizonChanged /\
  Not g.dragHorizonChanged /\
  Not g.primordialDeltaEnabled /\
  Not g.polarizationSourceDeltaEnabled /\
  g.earlyAcousticWindowEnabled /\
  g.earlyISWDeltaEnabled /\
  Not g.lateISWLeakage /\
  g.eeUnlensedUnchanged /\
  g.cPhiPhiUnchanged /\
  g.ttUnlensedMayChange /\
  g.teUnlensedMayChange /\
  g.lambdaZeroIdentityPassed /\
  g.smallLambdaContinuityPassed

theorem acoustic_ready_implies_gate
    (g : AcousticDrivingDeltaGate)
    (hPolicy : acousticDrivingReady g -> g.acousticDrivingDeltaGatePassed)
    (h : acousticDrivingReady g) :
    g.acousticDrivingDeltaGatePassed := by
  exact hPolicy h

theorem acoustic_gate_allows_controlled_trial_not_full_verdict
    (g : AcousticDrivingDeltaGate)
    (hTrial : g.acousticDrivingDeltaGatePassed -> g.officialPlanckAcousticDrivingTrialAllowed)
    (hNoFull : g.acousticDrivingDeltaGatePassed -> Not g.fullNativeZ4Verdict)
    (h : g.acousticDrivingDeltaGatePassed) :
    g.officialPlanckAcousticDrivingTrialAllowed /\ Not g.fullNativeZ4Verdict := by
  exact And.intro (hTrial h) (hNoFull h)

end P0EFTJanusZ4AcousticDrivingDeltaGate
end JanusFormal
