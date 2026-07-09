import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4SWISWSourceDeltaGate

namespace JanusFormal
namespace P0EFTJanusZ4WeylLateISWConsistencyGate

set_option autoImplicit false

structure WeylLateISWConsistencyGate where
  sharedWeylDeltaDeclared : Prop
  lensingKernelUsesSharedWeyl : Prop
  lateISWUsesTimeDerivativeOfSharedWeyl : Prop
  independentLensingWeylDelta : Prop
  independentISWWeylDelta : Prop
  earlyISWDeltaEnabled : Prop
  recombinationSourceUnchanged : Prop
  visibilityUnchanged : Prop
  acousticDrivingUnchanged : Prop
  polarizationSourceUnchanged : Prop
  noEarlyISWLeakage : Prop
  lambdaZeroIdentityPassed : Prop
  smallLambdaContinuityPassed : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  consistencyGatePassed : Prop
  officialPlanckWeylLateISWTrialAllowed : Prop

def sharedWeylLateISWReady (g : WeylLateISWConsistencyGate) : Prop :=
  g.sharedWeylDeltaDeclared /\
  g.lensingKernelUsesSharedWeyl /\
  g.lateISWUsesTimeDerivativeOfSharedWeyl /\
  Not g.independentLensingWeylDelta /\
  Not g.independentISWWeylDelta /\
  Not g.earlyISWDeltaEnabled /\
  g.recombinationSourceUnchanged /\
  g.visibilityUnchanged /\
  g.acousticDrivingUnchanged /\
  g.polarizationSourceUnchanged /\
  g.noEarlyISWLeakage /\
  g.lambdaZeroIdentityPassed /\
  g.smallLambdaContinuityPassed /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed

theorem shared_weyl_late_isw_ready_implies_gate
    (g : WeylLateISWConsistencyGate)
    (hPolicy : sharedWeylLateISWReady g -> g.consistencyGatePassed)
    (h : sharedWeylLateISWReady g) :
    g.consistencyGatePassed := by
  exact hPolicy h

theorem consistency_gate_allows_controlled_trial
    (g : WeylLateISWConsistencyGate)
    (hPolicy : g.consistencyGatePassed -> g.officialPlanckWeylLateISWTrialAllowed)
    (h : g.consistencyGatePassed) :
    g.officialPlanckWeylLateISWTrialAllowed := by
  exact hPolicy h

end P0EFTJanusZ4WeylLateISWConsistencyGate
end JanusFormal
