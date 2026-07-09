namespace JanusFormal
namespace P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate

set_option autoImplicit false

structure Z2SigmaCMBBoltzmannBibliographyGate where
  maBertschingerSourceFound : Prop
  cambClassSourceFound : Prop
  photonPolarizationHierarchySourceFound : Prop
  completeZ2SigmaCMBBoltzmannEquationsFound : Prop
  localCMBDerivationRequired : Prop

def bibliographySupportsButDoesNotCloseCMB
    (g : Z2SigmaCMBBoltzmannBibliographyGate) : Prop :=
  g.maBertschingerSourceFound /\
  g.cambClassSourceFound /\
  g.photonPolarizationHierarchySourceFound /\
  Not g.completeZ2SigmaCMBBoltzmannEquationsFound /\
  g.localCMBDerivationRequired

theorem missing_z2_sigma_cmb_requires_local_derivation
    (g : Z2SigmaCMBBoltzmannBibliographyGate)
    (h : bibliographySupportsButDoesNotCloseCMB g) :
    g.localCMBDerivationRequired := by
  exact h.2.2.2.2

end P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate
end JanusFormal
