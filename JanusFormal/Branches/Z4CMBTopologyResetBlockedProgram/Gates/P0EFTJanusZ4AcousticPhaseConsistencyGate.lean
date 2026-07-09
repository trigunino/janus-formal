import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4OfficialPlanckAcousticDrivingDeltaTrial

namespace JanusFormal
namespace P0EFTJanusZ4AcousticPhaseConsistencyGate

set_option autoImplicit false

structure AcousticPhaseConsistencyGate where
  refinedEarlyISWOnlyScan : Prop
  officialLikelihoodExecuted : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  polarizationSourceDeltaEnabled : Prop
  eeUnchangedByConstruction : Prop
  cPhiPhiUnchangedByConstruction : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  teZeroCrossingContinuous : Prop
  teSignCheckPassed : Prop
  bestLambdaNotScanEdge : Prop
  channelBreakdownAvailable : Prop
  planckSuccessVerdict : Prop
  acousticPhaseConsistencyGatePassed : Prop
  polarizationSourceDeltaGateAllowed : Prop

def phaseConsistencyReady (g : AcousticPhaseConsistencyGate) : Prop :=
  g.refinedEarlyISWOnlyScan /\
  g.officialLikelihoodExecuted /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.polarizationSourceDeltaEnabled /\
  g.eeUnchangedByConstruction /\
  g.cPhiPhiUnchangedByConstruction /\
  Not g.recombinationDeltaEnabled /\
  Not g.visibilityDeltaEnabled /\
  g.teZeroCrossingContinuous /\
  g.teSignCheckPassed /\
  g.bestLambdaNotScanEdge /\
  g.channelBreakdownAvailable

theorem phase_ready_implies_gate
    (g : AcousticPhaseConsistencyGate)
    (hPolicy : phaseConsistencyReady g -> g.acousticPhaseConsistencyGatePassed)
    (h : phaseConsistencyReady g) :
    g.acousticPhaseConsistencyGatePassed := by
  exact hPolicy h

theorem phase_gate_policy
    (g : AcousticPhaseConsistencyGate)
    (hPolar : g.acousticPhaseConsistencyGatePassed -> g.polarizationSourceDeltaGateAllowed)
    (hNoVerdict : g.acousticPhaseConsistencyGatePassed -> Not g.planckSuccessVerdict)
    (h : g.acousticPhaseConsistencyGatePassed) :
    g.polarizationSourceDeltaGateAllowed /\ Not g.planckSuccessVerdict := by
  exact And.intro (hPolar h) (hNoVerdict h)

end P0EFTJanusZ4AcousticPhaseConsistencyGate
end JanusFormal
