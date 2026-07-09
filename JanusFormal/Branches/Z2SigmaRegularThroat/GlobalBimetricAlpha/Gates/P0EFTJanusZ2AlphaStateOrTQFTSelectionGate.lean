namespace JanusFormal
namespace P0EFTJanusZ2AlphaStateOrTQFTSelectionGate

set_option autoImplicit false

structure AlphaStateOrTQFTSelectionGate where
  microcanonicalRouteReady : Prop
  tqftRouteReady : Prop
  uniqueAlphaSelectorDerived : Prop
  alphaStateSectorRequired : Prop
  noFitClaimBlockedWithoutSelection : Prop

def stateSectorFallback (g : AlphaStateOrTQFTSelectionGate) : Prop :=
  ¬ g.microcanonicalRouteReady ∧ ¬ g.tqftRouteReady

def nonCircularSelectorReady (g : AlphaStateOrTQFTSelectionGate) : Prop :=
  g.microcanonicalRouteReady ∨ g.tqftRouteReady

def noFitPredictionAllowed (g : AlphaStateOrTQFTSelectionGate) : Prop :=
  nonCircularSelectorReady g ∧ g.uniqueAlphaSelectorDerived

theorem only_fallback_without_selector
    (g : AlphaStateOrTQFTSelectionGate)
    (_hState : g.alphaStateSectorRequired)
    (_hNoFit : g.noFitClaimBlockedWithoutSelection)
    (hSelector : ¬ nonCircularSelectorReady g) :
    stateSectorFallback g := by
  constructor
  · intro hM
    have hNoSel : ¬ nonCircularSelectorReady g := hSelector
    exact hNoSel (Or.inl hM)
  · intro hT
    have hNoSel : ¬ nonCircularSelectorReady g := hSelector
    exact hNoSel (Or.inr hT)

end P0EFTJanusZ2AlphaStateOrTQFTSelectionGate
end JanusFormal
