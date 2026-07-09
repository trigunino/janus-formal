import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PolarizationEdgePhaseAuditGate

namespace JanusFormal
namespace P0EFTJanusZ4AcousticPolarizationJointConsistencyGate

set_option autoImplicit false

structure AcousticPolarizationJointConsistencyGate where
  localTwoDimensionalScan : Prop
  officialLikelihoodExecuted : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  soundHorizonChanged : Prop
  dragRulerChanged : Prop
  primordialDeltaEnabled : Prop
  lensingCPhiPhiFrozen : Prop
  slipFrozen : Prop
  temperatureSourceTagged : Prop
  polarizationSourceTagged : Prop
  theta2ClosureComplete : Prop
  phaseGuardsPassed : Prop
  interactionTermSmall : Prop
  gatePassed : Prop
  theta2ClosureRecommended : Prop
  fullPlanckVerdict : Prop

def jointReady (g : AcousticPolarizationJointConsistencyGate) : Prop :=
  g.localTwoDimensionalScan /\
  g.officialLikelihoodExecuted /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.recombinationDeltaEnabled /\
  Not g.visibilityDeltaEnabled /\
  Not g.backgroundProjectionChanged /\
  Not g.soundHorizonChanged /\
  Not g.dragRulerChanged /\
  Not g.primordialDeltaEnabled /\
  g.lensingCPhiPhiFrozen /\
  g.slipFrozen /\
  g.temperatureSourceTagged /\
  g.polarizationSourceTagged /\
  g.phaseGuardsPassed /\
  g.interactionTermSmall

theorem ready_implies_joint_gate
    (g : AcousticPolarizationJointConsistencyGate)
    (hPolicy : jointReady g -> g.gatePassed)
    (h : jointReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem joint_gate_is_not_full_planck_verdict
    (g : AcousticPolarizationJointConsistencyGate)
    (hPolicy : g.gatePassed -> Not g.fullPlanckVerdict /\ g.theta2ClosureRecommended)
    (h : g.gatePassed) :
    Not g.fullPlanckVerdict /\ g.theta2ClosureRecommended := by
  exact hPolicy h

theorem incomplete_theta2_blocks_native_promotion
    (g : AcousticPolarizationJointConsistencyGate)
    (hPolicy : Not g.theta2ClosureComplete -> Not g.fullPlanckVerdict)
    (h : Not g.theta2ClosureComplete) :
    Not g.fullPlanckVerdict := by
  exact hPolicy h

end P0EFTJanusZ4AcousticPolarizationJointConsistencyGate
end JanusFormal
