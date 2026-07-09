namespace JanusFormal
namespace P0EFTJanusZ2SigmaDistanceBAOBibliographyGate

set_option autoImplicit false

structure Z2SigmaDistanceBAOBibliographyGate where
  janusPhotonGeodesicSourceFound : Prop
  standardFLRWDistanceSourceFound : Prop
  etheringtonReciprocitySourceFound : Prop
  baoSoundHorizonSourceFound : Prop
  completeSigmaPhotonDistanceMapFound : Prop
  completeZ2SigmaSoundRulerFound : Prop
  localDistanceAndRulerDerivationRequired : Prop

def bibliographySupportsButDoesNotCloseDistanceBAO
    (g : Z2SigmaDistanceBAOBibliographyGate) : Prop :=
  g.janusPhotonGeodesicSourceFound /\
  g.standardFLRWDistanceSourceFound /\
  g.etheringtonReciprocitySourceFound /\
  g.baoSoundHorizonSourceFound /\
  Not g.completeSigmaPhotonDistanceMapFound /\
  Not g.completeZ2SigmaSoundRulerFound /\
  g.localDistanceAndRulerDerivationRequired

theorem missing_sigma_distance_and_ruler_requires_local_derivation
    (g : Z2SigmaDistanceBAOBibliographyGate)
    (h : bibliographySupportsButDoesNotCloseDistanceBAO g) :
    g.localDistanceAndRulerDerivationRequired := by
  exact h.2.2.2.2.2.2

end P0EFTJanusZ2SigmaDistanceBAOBibliographyGate
end JanusFormal
