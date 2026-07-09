namespace JanusFormal
namespace P0EFTScreenedGeffCAMBGate

set_option autoImplicit false

structure ScreenedGeffCAMBGate where
  fullBackgroundBoost : Prop
  screenedPerturbationBoost : Prop
  rdWindowHit : Prop
  planckImproves : Prop
  screeningFactorDerived : Prop

def gatePasses (g : ScreenedGeffCAMBGate) : Prop :=
  g.fullBackgroundBoost /\
  g.screenedPerturbationBoost /\
  g.rdWindowHit /\
  g.planckImproves

def noFitReady (g : ScreenedGeffCAMBGate) : Prop :=
  gatePasses g /\ g.screeningFactorDerived

theorem gate_still_requires_screening_derivation
    (g : ScreenedGeffCAMBGate)
    (_hGate : gatePasses g)
    (hMissing : Not g.screeningFactorDerived) :
    Not (noFitReady g) := by
  intro h
  exact hMissing h.right

end P0EFTScreenedGeffCAMBGate
end JanusFormal
