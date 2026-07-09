import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TEEETransportSmoothnessGate

namespace JanusFormal
namespace P0EFTJanusZ4AcousticPolarizationClosedTheta2JointGate

set_option autoImplicit false

structure AcousticPolarizationClosedTheta2JointGate where
  localSmallScan : Prop
  officialLikelihoodExecuted : Prop
  tightCouplingDerivedTheta2 : Prop
  boltzmannHierarchyClosed : Prop
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
  jointDeltaNegative : Prop
  interactionTermAcceptable : Prop
  hardPhaseGuardPassed : Prop
  teSmoothnessGuardPassed : Prop
  eeSmoothnessGuardPassed : Prop
  candidatePromoted : Prop
  fullPlanckVerdict : Prop
  boltzmannHierarchyClosureRecommended : Prop

def closedTheta2JointReady (g : AcousticPolarizationClosedTheta2JointGate) : Prop :=
  g.localSmallScan /\
  g.officialLikelihoodExecuted /\
  g.tightCouplingDerivedTheta2 /\
  Not g.boltzmannHierarchyClosed /\
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
  g.jointDeltaNegative /\
  g.interactionTermAcceptable /\
  g.hardPhaseGuardPassed /\
  g.teSmoothnessGuardPassed /\
  g.eeSmoothnessGuardPassed

theorem ready_implies_effective_candidate
    (g : AcousticPolarizationClosedTheta2JointGate)
    (hPolicy : closedTheta2JointReady g -> g.candidatePromoted)
    (h : closedTheta2JointReady g) :
    g.candidatePromoted := by
  exact hPolicy h

theorem candidate_is_not_full_planck_verdict
    (g : AcousticPolarizationClosedTheta2JointGate)
    (hPolicy : g.candidatePromoted -> Not g.fullPlanckVerdict /\ g.boltzmannHierarchyClosureRecommended)
    (h : g.candidatePromoted) :
    Not g.fullPlanckVerdict /\ g.boltzmannHierarchyClosureRecommended := by
  exact hPolicy h

end P0EFTJanusZ4AcousticPolarizationClosedTheta2JointGate
end JanusFormal
