namespace JanusFormal
namespace P0EFTImmirziCoefficientConstraintSolver

set_option autoImplicit false

structure ImmirziCoefficientConstraintSolver where
  momentumConservationConstraint : Prop
  shearCompatibilityConstraint : Prop
  independentHolstStressConstraint : Prop
  uniqueCoefficientsDerived : Prop

def minimalConstraintsPresent (s : ImmirziCoefficientConstraintSolver) : Prop :=
  s.momentumConservationConstraint /\
  s.shearCompatibilityConstraint

def sufficientForUniqueCoefficients (s : ImmirziCoefficientConstraintSolver) : Prop :=
  minimalConstraintsPresent s /\
  s.independentHolstStressConstraint

theorem minimal_constraints_do_not_close_coefficients
    (s : ImmirziCoefficientConstraintSolver)
    (_hMin : minimalConstraintsPresent s)
    (hMissing : Not s.independentHolstStressConstraint) :
    Not (sufficientForUniqueCoefficients s) := by
  intro h
  exact hMissing h.right

theorem unique_coefficients_require_independent_holst_stress
    (s : ImmirziCoefficientConstraintSolver)
    (hUnique : s.uniqueCoefficientsDerived)
    (hRule : s.uniqueCoefficientsDerived -> s.independentHolstStressConstraint) :
    s.independentHolstStressConstraint := by
  exact hRule hUnique

end P0EFTImmirziCoefficientConstraintSolver
end JanusFormal
