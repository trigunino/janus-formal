namespace JanusFormal
namespace P0EFTJanusZ2AlphaObservationalFitGate

set_option autoImplicit false

structure AlphaObservationalFitGate where
  q0Observable : Prop
  alphaDimensionalMapReady : Prop
  snAvailable : Prop
  baoAvailable : Prop
  hzAvailable : Prop
  noFitClaim : Prop
  boundaryLimited : Prop

def backgroundObservationalFitReady (g : AlphaObservationalFitGate) : Prop :=
  g.q0Observable /\ g.snAvailable /\ g.baoAvailable

def fullAlphaFitReady (g : AlphaObservationalFitGate) : Prop :=
  backgroundObservationalFitReady g /\ g.alphaDimensionalMapReady

theorem q0_fit_without_dimensional_map_is_not_full_alpha_fit
    (g : AlphaObservationalFitGate)
    (_h : backgroundObservationalFitReady g)
    (hNoMap : Not g.alphaDimensionalMapReady) :
    Not (fullAlphaFitReady g) := by
  intro h
  exact hNoMap h.2

theorem observational_fit_does_not_imply_no_fit
    (g : AlphaObservationalFitGate)
    (_h : backgroundObservationalFitReady g)
    (hNoFit : Not g.noFitClaim) :
    Not g.noFitClaim := hNoFit

end P0EFTJanusZ2AlphaObservationalFitGate
end JanusFormal
