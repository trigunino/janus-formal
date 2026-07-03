namespace JanusFormal
namespace P0EFTJanusZ2SigmaGrowthBibliographyGate

set_option autoImplicit false

structure Z2SigmaGrowthBibliographyGate where
  standardLinearPerturbationSourceFound : Prop
  bimetricPerturbationSourceFound : Prop
  einsteinCartanPerturbationSourceFound : Prop
  janusStructureGrowthSourceFound : Prop
  completeZ2SigmaGrowthEquationsFound : Prop
  localGrowthDerivationRequired : Prop

def bibliographySupportsButDoesNotCloseGrowth
    (g : Z2SigmaGrowthBibliographyGate) : Prop :=
  g.standardLinearPerturbationSourceFound /\
  g.bimetricPerturbationSourceFound /\
  g.einsteinCartanPerturbationSourceFound /\
  g.janusStructureGrowthSourceFound /\
  Not g.completeZ2SigmaGrowthEquationsFound /\
  g.localGrowthDerivationRequired

theorem missing_z2_sigma_growth_requires_local_derivation
    (g : Z2SigmaGrowthBibliographyGate)
    (h : bibliographySupportsButDoesNotCloseGrowth g) :
    g.localGrowthDerivationRequired := by
  exact h.2.2.2.2.2

end P0EFTJanusZ2SigmaGrowthBibliographyGate
end JanusFormal
