namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundBibliographyGate

set_option autoImplicit false

structure Z2SigmaBackgroundBibliographyGate where
  janusProjectiveTunnelTopologySourceFound : Prop
  janusBimetricFLRWSourceFound : Prop
  junctionBoundaryFormalismSourceFound : Prop
  einsteinCartanHolstCosmologySourceFound : Prop
  completeZ2SigmaBackgroundEquationsFound : Prop
  localDerivationRequired : Prop

def bibliographySupportsButDoesNotCloseBackground
    (g : Z2SigmaBackgroundBibliographyGate) : Prop :=
  g.janusProjectiveTunnelTopologySourceFound /\
  g.janusBimetricFLRWSourceFound /\
  g.junctionBoundaryFormalismSourceFound /\
  g.einsteinCartanHolstCosmologySourceFound /\
  Not g.completeZ2SigmaBackgroundEquationsFound /\
  g.localDerivationRequired

theorem missing_complete_background_source_requires_local_derivation
    (g : Z2SigmaBackgroundBibliographyGate)
    (h : bibliographySupportsButDoesNotCloseBackground g) :
    g.localDerivationRequired := by
  exact h.2.2.2.2.2

end P0EFTJanusZ2SigmaBackgroundBibliographyGate
end JanusFormal
