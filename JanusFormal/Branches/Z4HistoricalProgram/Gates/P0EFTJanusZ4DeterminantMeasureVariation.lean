namespace JanusFormal
namespace P0EFTJanusZ4DeterminantMeasureVariation

set_option autoImplicit false

structure DeterminantMeasureVariation where
  determinantRatioDeclared : Prop
  logarithmicVariationDeclared : Prop
  reciprocalVariationConsistent : Prop
  plusMeasureTermTracked : Prop
  minusMeasureTermTracked : Prop
  insertedIntoFullActionVariation : Prop

def measureVariationScaffoldReady (m : DeterminantMeasureVariation) : Prop :=
  m.determinantRatioDeclared /\
  m.logarithmicVariationDeclared /\
  m.reciprocalVariationConsistent /\
  m.plusMeasureTermTracked /\
  m.minusMeasureTermTracked

def measureVariationPhysicalReady (m : DeterminantMeasureVariation) : Prop :=
  measureVariationScaffoldReady m /\
  m.insertedIntoFullActionVariation

theorem measure_scaffold_does_not_close_full_action
    (m : DeterminantMeasureVariation)
    (_ready : measureVariationScaffoldReady m)
    (hMissing : Not m.insertedIntoFullActionVariation) :
    Not (measureVariationPhysicalReady m) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4DeterminantMeasureVariation
end JanusFormal
