import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4IonizationEquilibriumSolution

namespace JanusFormal
namespace P0EFTJanusZ4IonizationODESolverTarget

set_option autoImplicit false

structure IonizationODESolverTarget where
  timeDependentPeeblesODEDeclared : Prop
  z4ExpansionRateInserted : Prop
  initialConditionDeclared : Prop
  boundedIonizationHistoryProduced : Prop
  visibilityBuiltFromHistory : Prop
  calibratedRecombinationCoefficientsUsed : Prop

def ionizationODESolverReady (i : IonizationODESolverTarget) : Prop :=
  i.timeDependentPeeblesODEDeclared /\
  i.z4ExpansionRateInserted /\
  i.initialConditionDeclared /\
  i.boundedIonizationHistoryProduced /\
  i.visibilityBuiltFromHistory

def physicalIonizationSolverReady (i : IonizationODESolverTarget) : Prop :=
  ionizationODESolverReady i /\
  i.calibratedRecombinationCoefficientsUsed

theorem ode_solver_requires_bounded_history
    (i : IonizationODESolverTarget)
    (h : ionizationODESolverReady i) :
    i.boundedIonizationHistoryProduced := by
  exact h.right.right.right.left

theorem ode_solver_does_not_imply_physical_coefficients
    (i : IonizationODESolverTarget)
    (_h : ionizationODESolverReady i)
    (hMissing : Not i.calibratedRecombinationCoefficientsUsed) :
    Not (physicalIonizationSolverReady i) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4IonizationODESolverTarget
end JanusFormal
