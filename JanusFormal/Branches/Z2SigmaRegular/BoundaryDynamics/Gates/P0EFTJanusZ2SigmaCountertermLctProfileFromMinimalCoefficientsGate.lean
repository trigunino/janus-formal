namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermLctProfileFromMinimalCoefficientsGate

set_option autoImplicit false

structure LctProfileFromMinimalCoefficientsGate where
  coefficientSolverPassed : Prop
  coefficientsActiveDerived : Prop
  noFittedCoefficients : Prop
  lctProfileWritten : Prop
  localRadialVariationConventionDeclared : Prop

def lctProfileFromCoefficientsReady
    (g : LctProfileFromMinimalCoefficientsGate) : Prop :=
  g.coefficientSolverPassed /\
  g.coefficientsActiveDerived /\
  g.noFittedCoefficients /\
  g.lctProfileWritten /\
  g.localRadialVariationConventionDeclared

theorem lct_profile_requires_coefficient_solver
    (g : LctProfileFromMinimalCoefficientsGate)
    (hReady : lctProfileFromCoefficientsReady g) :
    g.coefficientSolverPassed := by
  exact hReady.1

end P0EFTJanusZ2SigmaCountertermLctProfileFromMinimalCoefficientsGate
end JanusFormal
