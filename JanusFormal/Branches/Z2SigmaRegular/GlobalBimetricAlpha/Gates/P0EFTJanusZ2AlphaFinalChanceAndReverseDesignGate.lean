namespace JanusFormal
namespace P0EFTJanusZ2AlphaFinalChanceAndReverseDesignGate

set_option autoImplicit false

structure AlphaFinalChanceGate where
  globalChargeValueDerived : Prop
  sectorQuantizationUnitDerived : Prop
  primitiveSectorSelected : Prop
  bimetricEGlobalLawDerived : Prop
  observationalSectorSelectionReady : Prop
  claimsNoFitFromObservation : Prop

def internalAlphaDerived (g : AlphaFinalChanceGate) : Prop :=
  g.globalChargeValueDerived \/
  (g.sectorQuantizationUnitDerived /\ g.primitiveSectorSelected) \/
  g.bimetricEGlobalLawDerived

def observationalSelectionHonest (g : AlphaFinalChanceGate) : Prop :=
  g.observationalSectorSelectionReady /\ Not g.claimsNoFitFromObservation

def alphaStateSectorStillRequired (g : AlphaFinalChanceGate) : Prop :=
  Not (internalAlphaDerived g)

theorem all_direct_internal_routes_missing_implies_state_sector_required
    (g : AlphaFinalChanceGate)
    (hCharge : Not g.globalChargeValueDerived)
    (hQuant : Not g.sectorQuantizationUnitDerived)
    (hBimetric : Not g.bimetricEGlobalLawDerived) :
    alphaStateSectorStillRequired g := by
  intro h
  rcases h with h | h | h
  · exact hCharge h
  · exact hQuant h.left
  · exact hBimetric h

theorem observation_selection_is_not_internal_derivation
    (g : AlphaFinalChanceGate)
    (_hObs : observationalSelectionHonest g)
    (hInternalMissing : alphaStateSectorStillRequired g) :
    Not (internalAlphaDerived g) := by
  exact hInternalMissing

end P0EFTJanusZ2AlphaFinalChanceAndReverseDesignGate
end JanusFormal
