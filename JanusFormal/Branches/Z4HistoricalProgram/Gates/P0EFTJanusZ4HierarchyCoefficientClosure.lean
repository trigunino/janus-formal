namespace JanusFormal
namespace P0EFTJanusZ4HierarchyCoefficientClosure

set_option autoImplicit false

structure HierarchyCoefficientClosure where
  soundSpeedDefinitionClosed : Prop
  baryonLoadingDefinitionClosed : Prop
  thomsonDragSignsClosed : Prop
  metricSourceSignsClosed : Prop
  z4BackgroundInputsRequired : Prop
  coefficientsDerivedFromZ4Action : Prop

def coefficientScaffoldReady (c : HierarchyCoefficientClosure) : Prop :=
  c.soundSpeedDefinitionClosed /\
  c.baryonLoadingDefinitionClosed /\
  c.thomsonDragSignsClosed /\
  c.metricSourceSignsClosed /\
  c.z4BackgroundInputsRequired

def coefficientPhysicalReady (c : HierarchyCoefficientClosure) : Prop :=
  coefficientScaffoldReady c /\
  c.coefficientsDerivedFromZ4Action

theorem coefficient_scaffold_does_not_imply_z4_action_derivation
    (c : HierarchyCoefficientClosure)
    (_ready : coefficientScaffoldReady c)
    (hMissing : Not c.coefficientsDerivedFromZ4Action) :
    Not (coefficientPhysicalReady c) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4HierarchyCoefficientClosure
end JanusFormal
