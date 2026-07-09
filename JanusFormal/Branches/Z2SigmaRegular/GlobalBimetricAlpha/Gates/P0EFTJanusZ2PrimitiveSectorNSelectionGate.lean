namespace JanusFormal
namespace P0EFTJanusZ2PrimitiveSectorNSelectionGate

set_option autoImplicit false

structure PrimitiveSectorNSelectionGate where
  sectorLatticeExists : Prop
  zeroSectorExcluded : Prop
  fusionForbidden : Prop
  splittingForbidden : Prop
  emptyPuncturesForbidden : Prop
  groundEnergyMonotoneInAbsN : Prop
  orientationIdentifiesSigns : Prop

def primitiveNSelected (g : PrimitiveSectorNSelectionGate) : Prop :=
  g.sectorLatticeExists /\
  g.zeroSectorExcluded /\
  g.fusionForbidden /\
  g.splittingForbidden /\
  g.emptyPuncturesForbidden /\
  g.groundEnergyMonotoneInAbsN /\
  g.orientationIdentifiesSigns

theorem missing_nonzero_blocks_primitive_selection
    (g : PrimitiveSectorNSelectionGate)
    (hMissing : Not g.zeroSectorExcluded) :
    Not (primitiveNSelected g) := by
  intro h
  exact hMissing h.right.left

theorem missing_monotonicity_blocks_primitive_selection
    (g : PrimitiveSectorNSelectionGate)
    (hMissing : Not g.groundEnergyMonotoneInAbsN) :
    Not (primitiveNSelected g) := by
  intro h
  exact hMissing h.right.right.right.right.right.left

end P0EFTJanusZ2PrimitiveSectorNSelectionGate
end JanusFormal
