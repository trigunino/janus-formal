namespace JanusFormal
namespace P0EFTJanusZ2BimetricVacuumAlphaSelectorGate

set_option autoImplicit false

structure BimetricVacuumAlphaSelectorGate where
  relativeSectorRatioReady : Prop
  absoluteDensityScaleReady : Prop
  rhoPlus0AbsReady : Prop
  occupationReady : Prop
  curvatureRadiusReady : Prop

def globalBimetricStateLawReady (g : BimetricVacuumAlphaSelectorGate) : Prop :=
  g.absoluteDensityScaleReady /\ g.rhoPlus0AbsReady

def alphaSelectorReady (g : BimetricVacuumAlphaSelectorGate) : Prop :=
  g.relativeSectorRatioReady /\ globalBimetricStateLawReady g

theorem relative_ratio_without_absolute_scale_blocks_selector
    (g : BimetricVacuumAlphaSelectorGate)
    (_hRatio : g.relativeSectorRatioReady)
    (hNoScale : Not g.absoluteDensityScaleReady) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hNoScale h.2.1

theorem missing_rho_plus_blocks_selector
    (g : BimetricVacuumAlphaSelectorGate)
    (hMissing : Not g.rhoPlus0AbsReady) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hMissing h.2.2

end P0EFTJanusZ2BimetricVacuumAlphaSelectorGate
end JanusFormal
