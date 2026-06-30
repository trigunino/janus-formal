import JanusFormal.P0EFTB4volSolderDerivation

namespace JanusFormal
namespace P0EFTMassShellLapseClosure

set_option autoImplicit false

structure MassShellLapseClosure where
  detLSolderAbsOne : Prop
  b4volReducedToTetradRatio : Prop
  receiverP0LapseFactorClosed : Prop
  activeSourceMeasureClosedConditionally : Prop

def activeMeasureConditionallyClosed (m : MassShellLapseClosure) : Prop :=
  m.detLSolderAbsOne /\
  m.b4volReducedToTetradRatio /\
  m.receiverP0LapseFactorClosed /\
  m.activeSourceMeasureClosedConditionally

theorem detL_and_lapse_close_active_measure_conditionally
    (m : MassShellLapseClosure)
    (hDet : m.detLSolderAbsOne)
    (hB4 : m.b4volReducedToTetradRatio)
    (hLapse : m.receiverP0LapseFactorClosed)
    (hActive : m.activeSourceMeasureClosedConditionally) :
    activeMeasureConditionallyClosed m := by
  exact And.intro hDet (And.intro hB4 (And.intro hLapse hActive))

end P0EFTMassShellLapseClosure
end JanusFormal
