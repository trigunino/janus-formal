namespace JanusFormal
namespace P0EFTJanusZ4ScalarClosure

set_option autoImplicit false

structure Z4ScalarClosure where
  poissonEquationDeclared : Prop
  momentumConstraintDeclared : Prop
  slipEquationDeclared : Prop
  continuityEquationDeclared : Prop
  eulerEquationDeclared : Prop
  gaugeFixingDeclared : Prop
  bianchiScalarResidualClosed : Prop
  coefficientsDerivedFromAction : Prop

def scalarClosureScaffoldReady (s : Z4ScalarClosure) : Prop :=
  s.poissonEquationDeclared /\
  s.momentumConstraintDeclared /\
  s.slipEquationDeclared /\
  s.continuityEquationDeclared /\
  s.eulerEquationDeclared /\
  s.gaugeFixingDeclared /\
  s.bianchiScalarResidualClosed

def scalarClosurePhysicalReady (s : Z4ScalarClosure) : Prop :=
  scalarClosureScaffoldReady s /\
  s.coefficientsDerivedFromAction

theorem scalar_scaffold_does_not_imply_action_coefficients
    (s : Z4ScalarClosure)
    (_ready : scalarClosureScaffoldReady s)
    (hMissing : Not s.coefficientsDerivedFromAction) :
    Not (scalarClosurePhysicalReady s) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4ScalarClosure
end JanusFormal
