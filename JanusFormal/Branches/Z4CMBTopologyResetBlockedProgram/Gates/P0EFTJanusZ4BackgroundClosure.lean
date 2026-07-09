namespace JanusFormal
namespace P0EFTJanusZ4BackgroundClosure

set_option autoImplicit false

structure Z4BackgroundClosure where
  masterDensityDefined : Prop
  friedmannConstraintDeclared : Prop
  accelerationConstraintDeclared : Prop
  continuityConstraintDeclared : Prop
  bianchiImpliesContinuity : Prop
  determinantMeasureCompatible : Prop
  coefficientsDerivedFromAction : Prop

def backgroundScaffoldReady (b : Z4BackgroundClosure) : Prop :=
  b.masterDensityDefined /\
  b.friedmannConstraintDeclared /\
  b.accelerationConstraintDeclared /\
  b.continuityConstraintDeclared /\
  b.bianchiImpliesContinuity /\
  b.determinantMeasureCompatible

def backgroundPhysicalReady (b : Z4BackgroundClosure) : Prop :=
  backgroundScaffoldReady b /\
  b.coefficientsDerivedFromAction

theorem background_scaffold_does_not_imply_action_coefficients
    (b : Z4BackgroundClosure)
    (_ready : backgroundScaffoldReady b)
    (hMissing : Not b.coefficientsDerivedFromAction) :
    Not (backgroundPhysicalReady b) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4BackgroundClosure
end JanusFormal
