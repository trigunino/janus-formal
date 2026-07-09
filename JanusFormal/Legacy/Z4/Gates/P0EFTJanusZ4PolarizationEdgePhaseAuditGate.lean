import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4OfficialPlanckPolarizationSourceDeltaTrial

namespace JanusFormal
namespace P0EFTJanusZ4PolarizationEdgePhaseAuditGate

set_option autoImplicit false

structure PolarizationEdgePhaseAuditGate where
  extendedLambdaEScan : Prop
  officialLikelihoodExecuted : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  primordialDeltaEnabled : Prop
  lensingDeltaEnabled : Prop
  deltaSlipZeroUntilDerived : Prop
  tePhaseGuardPassed : Prop
  eePeakGuardPassed : Prop
  ttInvariantUnderLambdaE : Prop
  cPhiPhiInvariantUnderLambdaE : Prop
  bestLambdaNotScanEdge : Prop
  incrementalGainNegative : Prop
  gatePassed : Prop
  jointAcousticPolarizationConsistencyAllowed : Prop
  theta2QuadrupoleClosureRecommended : Prop

def polarizationEdgeReady (g : PolarizationEdgePhaseAuditGate) : Prop :=
  g.extendedLambdaEScan /\
  g.officialLikelihoodExecuted /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.recombinationDeltaEnabled /\
  Not g.visibilityDeltaEnabled /\
  Not g.backgroundProjectionChanged /\
  Not g.primordialDeltaEnabled /\
  Not g.lensingDeltaEnabled /\
  g.deltaSlipZeroUntilDerived /\
  g.tePhaseGuardPassed /\
  g.eePeakGuardPassed /\
  g.ttInvariantUnderLambdaE /\
  g.cPhiPhiInvariantUnderLambdaE /\
  g.bestLambdaNotScanEdge /\
  g.incrementalGainNegative

theorem ready_implies_edge_phase_gate
    (g : PolarizationEdgePhaseAuditGate)
    (hPolicy : polarizationEdgeReady g -> g.gatePassed)
    (h : polarizationEdgeReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem failed_edge_gate_can_recommend_theta2
    (g : PolarizationEdgePhaseAuditGate)
    (hPolicy : Not g.gatePassed -> g.theta2QuadrupoleClosureRecommended)
    (h : Not g.gatePassed) :
    g.theta2QuadrupoleClosureRecommended := by
  exact hPolicy h

end P0EFTJanusZ4PolarizationEdgePhaseAuditGate
end JanusFormal
