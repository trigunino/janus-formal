namespace JanusFormal
namespace P0EFTJanusZ4NeutrinoHierarchyTarget

set_option autoImplicit false

structure NeutrinoHierarchyTarget where
  monopoleEquationDeclared : Prop
  dipoleEquationDeclared : Prop
  quadrupoleEquationDeclared : Prop
  higherMultipoleRecursionDeclared : Prop
  anisotropicStressFeedsSlip : Prop
  z4MetricInputsRequired : Prop
  hierarchyCoefficientsDerived : Prop

def neutrinoTargetReady (n : NeutrinoHierarchyTarget) : Prop :=
  n.monopoleEquationDeclared /\
  n.dipoleEquationDeclared /\
  n.quadrupoleEquationDeclared /\
  n.higherMultipoleRecursionDeclared /\
  n.anisotropicStressFeedsSlip /\
  n.z4MetricInputsRequired

def neutrinoPhysicalReady (n : NeutrinoHierarchyTarget) : Prop :=
  neutrinoTargetReady n /\
  n.hierarchyCoefficientsDerived

theorem neutrino_target_does_not_imply_physical_hierarchy
    (n : NeutrinoHierarchyTarget)
    (_ready : neutrinoTargetReady n)
    (hMissing : Not n.hierarchyCoefficientsDerived) :
    Not (neutrinoPhysicalReady n) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4NeutrinoHierarchyTarget
end JanusFormal
