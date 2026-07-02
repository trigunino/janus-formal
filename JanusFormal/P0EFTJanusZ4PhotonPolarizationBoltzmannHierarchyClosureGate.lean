import JanusFormal.P0EFTJanusZ4AcousticPolarizationClosedTheta2JointGate

namespace JanusFormal
namespace P0EFTJanusZ4PhotonPolarizationBoltzmannHierarchyClosureGate

set_option autoImplicit false

structure PhotonPolarizationBoltzmannHierarchyClosureGate where
  scalarModeOnly : Prop
  bModesDisabledOrGROnly : Prop
  thetaMultipolesDeclared : Prop
  eMultipolesDeclared : Prop
  collisionTermsDeclared : Prop
  opacityRateFrozenGRVisibilityBackend : Prop
  piSourceDerivedFromMultipoles : Prop
  theta2FreeSourceTag : Prop
  directEEPatch : Prop
  directTEPatch : Prop
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
  tightCouplingRegimeDeclared : Prop
  transitionRegimeDeclared : Prop
  freeStreamingRegimeDeclared : Prop
  tcaSwitchSmoothnessPassed : Prop
  strongTCASuppressionPassed : Prop
  lmaxConvergencePassed : Prop
  hierarchyClosedEffective : Prop
  gatePassed : Prop
  fullPlanckVerdict : Prop
  closedBoltzmannTrialRecommended : Prop

def hierarchyClosureReady (g : PhotonPolarizationBoltzmannHierarchyClosureGate) : Prop :=
  g.scalarModeOnly /\
  g.bModesDisabledOrGROnly /\
  g.thetaMultipolesDeclared /\
  g.eMultipolesDeclared /\
  g.collisionTermsDeclared /\
  g.opacityRateFrozenGRVisibilityBackend /\
  g.piSourceDerivedFromMultipoles /\
  Not g.theta2FreeSourceTag /\
  Not g.directEEPatch /\
  Not g.directTEPatch /\
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
  g.tightCouplingRegimeDeclared /\
  g.transitionRegimeDeclared /\
  g.freeStreamingRegimeDeclared /\
  g.tcaSwitchSmoothnessPassed /\
  g.strongTCASuppressionPassed /\
  g.lmaxConvergencePassed /\
  g.hierarchyClosedEffective

theorem ready_implies_hierarchy_gate
    (g : PhotonPolarizationBoltzmannHierarchyClosureGate)
    (hPolicy : hierarchyClosureReady g -> g.gatePassed)
    (h : hierarchyClosureReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem hierarchy_gate_is_not_full_planck_verdict
    (g : PhotonPolarizationBoltzmannHierarchyClosureGate)
    (hPolicy : g.gatePassed -> Not g.fullPlanckVerdict /\ g.closedBoltzmannTrialRecommended)
    (h : g.gatePassed) :
    Not g.fullPlanckVerdict /\ g.closedBoltzmannTrialRecommended := by
  exact hPolicy h

end P0EFTJanusZ4PhotonPolarizationBoltzmannHierarchyClosureGate
end JanusFormal
