namespace JanusFormal
namespace P0EFTJanusSectorTheoryV0Gate

set_option autoImplicit false

structure SectorTheoryV0Gate where
  sectorLawsDeclared : Prop
  noFitAlphaGenerated : Prop
  observationalSectorScanAvailable : Prop
  magicFitForbidden : Prop
  observationSelectedSectorDeclared : Prop

def honestSectorTheoryStatus (g : SectorTheoryV0Gate) : Prop :=
  g.sectorLawsDeclared /\
  Not g.noFitAlphaGenerated /\
  g.observationalSectorScanAvailable /\
  g.magicFitForbidden /\
  g.observationSelectedSectorDeclared

theorem sector_theory_v0_is_observation_selection_not_no_fit
    (g : SectorTheoryV0Gate)
    (h : honestSectorTheoryStatus g) :
    Not g.noFitAlphaGenerated := by
  exact h.right.left

end P0EFTJanusSectorTheoryV0Gate
end JanusFormal
