import JanusFormal.Branches.AsymptoticNullBoundaryCharges.Gates.P0EFTJanusAsymptoticNullBoundaryChargeDerivationGate

namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundaryAlphaBridgeGate

set_option autoImplicit false

structure AsymptoticNullBoundaryChargesAlphaBridgeGate where
  boundaryMassChargeReady : Prop
  MBridgeDerived : Prop
  alphaMBridgeRelationDeclared : Prop
  sectorSelectionOrQuantizationDerived : Prop
  alphaGeneratedNoFit : Prop

def alphaFromBoundaryChargeReady (g : AsymptoticNullBoundaryChargesAlphaBridgeGate) : Prop :=
  g.boundaryMassChargeReady /\
  g.MBridgeDerived /\
  g.alphaMBridgeRelationDeclared /\
  g.sectorSelectionOrQuantizationDerived /\
  g.alphaGeneratedNoFit

theorem missing_sector_selection_blocks_no_fit_alpha
    (g : AsymptoticNullBoundaryChargesAlphaBridgeGate)
    (hMissing : Not g.sectorSelectionOrQuantizationDerived) :
    Not (alphaFromBoundaryChargeReady g) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTJanusAsymptoticNullBoundaryAlphaBridgeGate
end JanusFormal
