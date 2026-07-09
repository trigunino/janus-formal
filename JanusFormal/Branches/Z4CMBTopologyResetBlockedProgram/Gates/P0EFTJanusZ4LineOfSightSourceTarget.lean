namespace JanusFormal
namespace P0EFTJanusZ4LineOfSightSourceTarget

set_option autoImplicit false

structure LineOfSightSourceTarget where
  visibilitySourceDeclared : Prop
  swSourceDeclared : Prop
  dopplerSourceDeclared : Prop
  iswSourceDeclared : Prop
  polarizationSourceDeclared : Prop
  z4MetricInputsRequired : Prop
  sourceCoefficientsDerived : Prop

def losTargetReady (s : LineOfSightSourceTarget) : Prop :=
  s.visibilitySourceDeclared /\
  s.swSourceDeclared /\
  s.dopplerSourceDeclared /\
  s.iswSourceDeclared /\
  s.polarizationSourceDeclared /\
  s.z4MetricInputsRequired

def losPhysicalReady (s : LineOfSightSourceTarget) : Prop :=
  losTargetReady s /\
  s.sourceCoefficientsDerived

theorem los_target_does_not_imply_physical_sources
    (s : LineOfSightSourceTarget)
    (_ready : losTargetReady s)
    (hMissing : Not s.sourceCoefficientsDerived) :
    Not (losPhysicalReady s) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4LineOfSightSourceTarget
end JanusFormal
