import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4AcousticPolarizationJointConsistencyGate

namespace JanusFormal
namespace P0EFTJanusZ4Theta2TightCouplingClosureGate

set_option autoImplicit false

structure Theta2TightCouplingClosureGate where
  previousSourceTaggedEffective : Prop
  tightCouplingDerivedEffective : Prop
  boltzmannHierarchyClosed : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  visibilityDeltaEnabled : Prop
  recombinationDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  soundHorizonChanged : Prop
  dragRulerChanged : Prop
  primordialDeltaEnabled : Prop
  lensingCPhiPhiFrozen : Prop
  slipFrozen : Prop
  metricSplitRespected : Prop
  dependsOnKOverKappadot : Prop
  dependsOnVelocityOrDipole : Prop
  dependsOnMetricDriving : Prop
  arbitraryEllFunction : Prop
  vanishesInStrongTightCoupling : Prop
  regularAtVisibilityPeak : Prop
  smoothInK : Prop
  smoothInTau : Prop
  gatePassed : Prop
  transportSmoothnessRecommended : Prop

def theta2ClosureReady (g : Theta2TightCouplingClosureGate) : Prop :=
  g.previousSourceTaggedEffective /\
  g.tightCouplingDerivedEffective /\
  Not g.boltzmannHierarchyClosed /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.visibilityDeltaEnabled /\
  Not g.recombinationDeltaEnabled /\
  Not g.backgroundProjectionChanged /\
  Not g.soundHorizonChanged /\
  Not g.dragRulerChanged /\
  Not g.primordialDeltaEnabled /\
  g.lensingCPhiPhiFrozen /\
  g.slipFrozen /\
  g.metricSplitRespected /\
  g.dependsOnKOverKappadot /\
  g.dependsOnVelocityOrDipole /\
  g.dependsOnMetricDriving /\
  Not g.arbitraryEllFunction /\
  g.vanishesInStrongTightCoupling /\
  g.regularAtVisibilityPeak /\
  g.smoothInK /\
  g.smoothInTau

theorem ready_implies_theta2_gate
    (g : Theta2TightCouplingClosureGate)
    (hPolicy : theta2ClosureReady g -> g.gatePassed)
    (h : theta2ClosureReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem theta2_gate_recommends_transport_smoothness
    (g : Theta2TightCouplingClosureGate)
    (hPolicy : g.gatePassed -> g.transportSmoothnessRecommended)
    (h : g.gatePassed) :
    g.transportSmoothnessRecommended := by
  exact hPolicy h

end P0EFTJanusZ4Theta2TightCouplingClosureGate
end JanusFormal
