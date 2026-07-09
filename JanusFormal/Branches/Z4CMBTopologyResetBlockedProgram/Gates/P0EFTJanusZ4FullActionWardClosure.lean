import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4AnomalyCancellationTarget

namespace JanusFormal
namespace P0EFTJanusZ4FullActionWardClosure

set_option autoImplicit false

structure FullActionWardClosure where
  currentPlusDeclared : Prop
  currentMinusDeclared : Prop
  determinantWeightedCurrentDeclared : Prop
  currentPlusCancelsWeightedMinus : Prop
  currentDivergenceVanishes : Prop
  anomalyVanishes : Prop
  obstructionVanishes : Prop

def currentConservationReady (w : FullActionWardClosure) : Prop :=
  w.currentPlusDeclared /\
  w.currentMinusDeclared /\
  w.determinantWeightedCurrentDeclared /\
  w.currentPlusCancelsWeightedMinus /\
  w.currentDivergenceVanishes

def fullActionWardClosureReady (w : FullActionWardClosure) : Prop :=
  currentConservationReady w /\
  w.anomalyVanishes /\
  w.obstructionVanishes

theorem closure_ready_gives_obstruction_zero
    (w : FullActionWardClosure)
    (h : fullActionWardClosureReady w) :
    w.obstructionVanishes := by
  exact h.right.right

theorem current_ready_gives_divergence_zero
    (w : FullActionWardClosure)
    (h : currentConservationReady w) :
    w.currentDivergenceVanishes := by
  exact h.right.right.right.right

end P0EFTJanusZ4FullActionWardClosure
end JanusFormal
