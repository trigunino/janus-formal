import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4IonizationHistoryClosure
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4VisibilityNormalizationClosure

namespace JanusFormal
namespace P0EFTJanusZ4IonizationEquilibriumSolution

set_option autoImplicit false

structure IonizationEquilibriumSolution where
  peeblesStationaryEquationSolved : Prop
  positiveRootSelected : Prop
  rootBoundedBetweenZeroAndOne : Prop
  z4ExpansionRateHeldExternal : Prop
  visibilityCanUseEquilibriumRoot : Prop
  fullTimeDependentIonizationSolved : Prop

def ionizationEquilibriumReady (i : IonizationEquilibriumSolution) : Prop :=
  i.peeblesStationaryEquationSolved /\
  i.positiveRootSelected /\
  i.rootBoundedBetweenZeroAndOne /\
  i.z4ExpansionRateHeldExternal /\
  i.visibilityCanUseEquilibriumRoot

def ionizationNonProxyReady (i : IonizationEquilibriumSolution) : Prop :=
  ionizationEquilibriumReady i /\
  i.fullTimeDependentIonizationSolved

theorem equilibrium_solution_requires_physical_root
    (i : IonizationEquilibriumSolution)
    (h : ionizationEquilibriumReady i) :
    i.rootBoundedBetweenZeroAndOne := by
  exact h.right.right.left

theorem equilibrium_solution_does_not_solve_full_history
    (i : IonizationEquilibriumSolution)
    (_h : ionizationEquilibriumReady i)
    (hMissing : Not i.fullTimeDependentIonizationSolved) :
    Not (ionizationNonProxyReady i) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4IonizationEquilibriumSolution
end JanusFormal
