import JanusFormal.P0EFTJanusZ4AcousticPhaseConsistencyGate

namespace JanusFormal
namespace P0EFTJanusZ4PlanckLensingInputDependenceGate

set_option autoImplicit false

structure PlanckLensingInputDependenceGate where
  cPhiPhiFrozen : Prop
  z4LensingDeltaEnabled : Prop
  primaryCMBDeltaEnabledInBD : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  officialLikelihoodExecuted : Prop
  primaryCMBDependenceDetected : Prop
  noIndependentCPhiPhiSignal : Prop
  combinedMatchesPrimaryCMBOnly : Prop
  gatePassed : Prop

def lensingInputDependenceReady (g : PlanckLensingInputDependenceGate) : Prop :=
  g.cPhiPhiFrozen /\
  Not g.z4LensingDeltaEnabled /\
  g.primaryCMBDeltaEnabledInBD /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  g.officialLikelihoodExecuted /\
  g.primaryCMBDependenceDetected /\
  g.noIndependentCPhiPhiSignal /\
  g.combinedMatchesPrimaryCMBOnly

theorem ready_implies_lensing_input_gate
    (g : PlanckLensingInputDependenceGate)
    (hPolicy : lensingInputDependenceReady g -> g.gatePassed)
    (h : lensingInputDependenceReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4PlanckLensingInputDependenceGate
end JanusFormal
