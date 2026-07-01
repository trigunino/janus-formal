import JanusFormal.P0EFTJanusZ4IonizationODESolverTarget

namespace JanusFormal
namespace P0EFTJanusZ4RecombinationCoefficientClosure

set_option autoImplicit false

structure RecombinationCoefficientClosure where
  sahaEquilibriumDeclared : Prop
  detailedBalanceRelationDeclared : Prop
  peeblesEquilibriumResidualClosed : Prop
  coefficientsPositive : Prop
  z4TemperatureInputRequired : Prop
  coefficientsCalibratedFromMicrophysics : Prop

def recombinationCoefficientClosureReady (r : RecombinationCoefficientClosure) : Prop :=
  r.sahaEquilibriumDeclared /\
  r.detailedBalanceRelationDeclared /\
  r.peeblesEquilibriumResidualClosed /\
  r.coefficientsPositive /\
  r.z4TemperatureInputRequired

def recombinationCoefficientPhysicalReady (r : RecombinationCoefficientClosure) : Prop :=
  recombinationCoefficientClosureReady r /\
  r.coefficientsCalibratedFromMicrophysics

theorem detailed_balance_closes_equilibrium_residual
    (r : RecombinationCoefficientClosure)
    (h : recombinationCoefficientClosureReady r) :
    r.peeblesEquilibriumResidualClosed := by
  exact h.right.right.left

theorem coefficient_closure_does_not_calibrate_microphysics
    (r : RecombinationCoefficientClosure)
    (_h : recombinationCoefficientClosureReady r)
    (hMissing : Not r.coefficientsCalibratedFromMicrophysics) :
    Not (recombinationCoefficientPhysicalReady r) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4RecombinationCoefficientClosure
end JanusFormal
