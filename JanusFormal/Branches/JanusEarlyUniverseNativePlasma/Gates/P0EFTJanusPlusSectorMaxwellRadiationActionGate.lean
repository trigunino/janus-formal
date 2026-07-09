namespace JanusFormal
namespace P0EFTJanusPlusSectorMaxwellRadiationActionGate

set_option autoImplicit false

structure PlusSectorMaxwellRadiationActionGate where
  fieldAPlusDeclared : Prop
  metricGPlusDeclared : Prop
  maxwellDensityDeclared : Prop
  minimalCouplingToGPlus : Prop
  crossSectorPhotonExchangeForbidden : Prop
  maxwellEomDeclared : Prop
  stressTensorDeclared : Prop
  stressTracefreeInFourDimensions : Prop
  noetherStressConservationOnShell : Prop
  compatibleWithPositivePhotonGeodesicAnchors : Prop
  explicitlyPaperNative : Prop
  classifiedAsMinimalStandardExtension : Prop

def maxwellRadiationActionReady
    (g : PlusSectorMaxwellRadiationActionGate) : Prop :=
  g.fieldAPlusDeclared /\
  g.metricGPlusDeclared /\
  g.maxwellDensityDeclared /\
  g.minimalCouplingToGPlus /\
  g.crossSectorPhotonExchangeForbidden /\
  g.maxwellEomDeclared /\
  g.stressTensorDeclared /\
  g.stressTracefreeInFourDimensions /\
  g.noetherStressConservationOnShell /\
  g.compatibleWithPositivePhotonGeodesicAnchors /\
  Not g.explicitlyPaperNative /\
  g.classifiedAsMinimalStandardExtension

theorem maxwell_extension_closes_plus_photon_stress_on_shell
    (g : PlusSectorMaxwellRadiationActionGate)
    (hReady : maxwellRadiationActionReady g) :
    g.noetherStressConservationOnShell /\ g.stressTracefreeInFourDimensions := by
  exact And.intro hReady.2.2.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.2.1

end P0EFTJanusPlusSectorMaxwellRadiationActionGate
end JanusFormal
