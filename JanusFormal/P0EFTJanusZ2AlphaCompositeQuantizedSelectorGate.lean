namespace JanusFormal
namespace P0EFTJanusZ2AlphaCompositeQuantizedSelectorGate

set_option autoImplicit false

structure AlphaCompositeQuantizedSelectorGate where
  chargeToAlphaMapDerived : Prop
  chargeLatticeQuantized : Prop
  chargeUnitDerived : Prop
  integerSectorAvailable : Prop
  primitiveSectorSelected : Prop
  noObservationFit : Prop
  noLegacyZ4 : Prop

def alphaSpectrumReady (g : AlphaCompositeQuantizedSelectorGate) : Prop :=
  g.chargeToAlphaMapDerived /\
  g.chargeLatticeQuantized /\
  g.chargeUnitDerived /\
  g.integerSectorAvailable /\
  g.noObservationFit /\
  g.noLegacyZ4

def uniqueAlphaReady (g : AlphaCompositeQuantizedSelectorGate) : Prop :=
  alphaSpectrumReady g /\ g.primitiveSectorSelected

theorem missing_charge_unit_blocks_spectrum
    (g : AlphaCompositeQuantizedSelectorGate)
    (hMissing : Not g.chargeUnitDerived) :
    Not (alphaSpectrumReady g) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_primitive_sector_blocks_unique_alpha
    (g : AlphaCompositeQuantizedSelectorGate)
    (hMissing : Not g.primitiveSectorSelected) :
    Not (uniqueAlphaReady g) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ2AlphaCompositeQuantizedSelectorGate
end JanusFormal
