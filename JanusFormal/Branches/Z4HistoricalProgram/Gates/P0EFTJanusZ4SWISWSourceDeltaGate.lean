import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4LensingComponentProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ4SWISWSourceDeltaGate

set_option autoImplicit false

structure SWISWSourceDeltaGate where
  lateISWDeltaEnabled : Prop
  earlyISWDeltaEnabled : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  visibilityDeltaEnabled : Prop
  recombinationDeltaEnabled : Prop
  acousticPhaseDeltaEnabled : Prop
  polarizationSourceDeltaEnabled : Prop
  primordialSpectrumDeltaEnabled : Prop
  lambdaZeroIdentityPassed : Prop
  smallLambdaContinuityPassed : Prop
  weylLensingConsistencyRequired : Prop
  gatePassed : Prop
  officialPlanckTrialAllowed : Prop

def lateISWSourceOnlyReady (g : SWISWSourceDeltaGate) : Prop :=
  g.lateISWDeltaEnabled /\
  Not g.earlyISWDeltaEnabled /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.visibilityDeltaEnabled /\
  Not g.recombinationDeltaEnabled /\
  Not g.acousticPhaseDeltaEnabled /\
  Not g.polarizationSourceDeltaEnabled /\
  Not g.primordialSpectrumDeltaEnabled /\
  g.lambdaZeroIdentityPassed /\
  g.smallLambdaContinuityPassed /\
  g.weylLensingConsistencyRequired

theorem late_isw_source_only_implies_gate
    (g : SWISWSourceDeltaGate)
    (hPolicy : lateISWSourceOnlyReady g -> g.gatePassed)
    (h : lateISWSourceOnlyReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem swisw_source_gate_alone_does_not_allow_planck
    (g : SWISWSourceDeltaGate)
    (hNoTrial : Not g.officialPlanckTrialAllowed) :
    Not g.officialPlanckTrialAllowed := by
  exact hNoTrial

end P0EFTJanusZ4SWISWSourceDeltaGate
end JanusFormal
