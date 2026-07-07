namespace JanusFormal
namespace P0EFTJanusZ2SigmaBoundaryLegEvaluationInventoryGate

set_option autoImplicit false

structure BoundaryLegEvaluationInventoryGate where
  plusBoundaryLegDeclared : Prop
  minusBoundaryLegDeclared : Prop
  plusNormalOrientationDeclared : Prop
  minusNormalOrientationDeclared : Prop
  lapseTimeGaugeDeclared : Prop
  referenceSubtractionDeclared : Prop
  jointCornerTermsAccounted : Prop
  boundaryChargeValueAvailable : Prop
  globalBimetricStateAvailable : Prop
  noSingleLegShortcut : Prop
  noReferenceZeroAsSourceShortcut : Prop

def symbolicLegEvaluationReady
    (g : BoundaryLegEvaluationInventoryGate) : Prop :=
  g.plusBoundaryLegDeclared /\
  g.minusBoundaryLegDeclared /\
  g.plusNormalOrientationDeclared /\
  g.minusNormalOrientationDeclared /\
  g.lapseTimeGaugeDeclared /\
  g.referenceSubtractionDeclared /\
  g.jointCornerTermsAccounted /\
  g.noSingleLegShortcut /\
  g.noReferenceZeroAsSourceShortcut

def numericStateReady
    (g : BoundaryLegEvaluationInventoryGate) : Prop :=
  symbolicLegEvaluationReady g /\
  g.boundaryChargeValueAvailable /\
  g.globalBimetricStateAvailable

theorem missing_charge_blocks_numeric_state
    (g : BoundaryLegEvaluationInventoryGate)
    (hMissing : Not g.boundaryChargeValueAvailable) :
    Not (numericStateReady g) := by
  intro hReady
  exact hMissing hReady.2.1

theorem missing_global_state_blocks_numeric_state
    (g : BoundaryLegEvaluationInventoryGate)
    (hMissing : Not g.globalBimetricStateAvailable) :
    Not (numericStateReady g) := by
  intro hReady
  exact hMissing hReady.2.2

end P0EFTJanusZ2SigmaBoundaryLegEvaluationInventoryGate
end JanusFormal
