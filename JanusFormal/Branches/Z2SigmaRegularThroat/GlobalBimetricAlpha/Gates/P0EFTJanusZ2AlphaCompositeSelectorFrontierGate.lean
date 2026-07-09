namespace JanusFormal
namespace P0EFTJanusZ2AlphaCompositeSelectorFrontierGate

set_option autoImplicit false

structure AlphaCompositeSelectorFrontierGate where
  momentMapExists : Prop
  chargeToAlphaMapExists : Prop
  chargeLatticeIntegralityDerived : Prop
  minimalMassUnitDerived : Prop
  primitiveNonzeroSectorRequired : Prop
  fusionSplittingForbidden : Prop
  primitiveNEqualsOneSelected : Prop

def mChargeReady (g : AlphaCompositeSelectorFrontierGate) : Prop :=
  g.momentMapExists /\
  g.chargeToAlphaMapExists /\
  g.chargeLatticeIntegralityDerived /\
  g.minimalMassUnitDerived

def primitiveNReady (g : AlphaCompositeSelectorFrontierGate) : Prop :=
  g.primitiveNonzeroSectorRequired /\
  g.fusionSplittingForbidden /\
  g.primitiveNEqualsOneSelected

def uniqueCompositeSelectorReady (g : AlphaCompositeSelectorFrontierGate) : Prop :=
  mChargeReady g /\ primitiveNReady g

theorem missing_mass_unit_blocks_unique_selector
    (g : AlphaCompositeSelectorFrontierGate)
    (hMissing : Not g.minimalMassUnitDerived) :
    Not (uniqueCompositeSelectorReady g) := by
  intro h
  exact hMissing h.left.right.right.right

theorem missing_primitive_n_blocks_unique_selector
    (g : AlphaCompositeSelectorFrontierGate)
    (hMissing : Not g.primitiveNEqualsOneSelected) :
    Not (uniqueCompositeSelectorReady g) := by
  intro h
  exact hMissing h.right.right.right

end P0EFTJanusZ2AlphaCompositeSelectorFrontierGate
end JanusFormal
