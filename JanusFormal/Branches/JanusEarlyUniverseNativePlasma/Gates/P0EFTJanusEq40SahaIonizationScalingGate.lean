namespace JanusFormal
namespace P0EFTJanusEq40SahaIonizationScalingGate

set_option autoImplicit false

structure Eq40SahaIonizationScalingGate where
  electronMassScalesA : Prop
  thermalEnergyTemperatureScalesAminusOne : Prop
  hScalesAThreeHalves : Prop
  baryonNumberDensityScalesAminusThree : Prop
  ionizationEnergyInvariant : Prop
  sahaPrefactorExponentMinusNineHalves : Prop
  sahaOverBaryonExponentMinusThreeHalves : Prop
  exponentialArgumentMinusConstTimesA : Prop
  nativeVisibilityMechanismAvailable : Prop
  absoluteTemperatureOrEtaBAnchorStillRequired : Prop

def eq40SahaIonizationReady (g : Eq40SahaIonizationScalingGate) : Prop :=
  g.electronMassScalesA /\
  g.thermalEnergyTemperatureScalesAminusOne /\
  g.hScalesAThreeHalves /\
  g.baryonNumberDensityScalesAminusThree /\
  g.ionizationEnergyInvariant /\
  g.sahaPrefactorExponentMinusNineHalves /\
  g.sahaOverBaryonExponentMinusThreeHalves /\
  g.exponentialArgumentMinusConstTimesA /\
  g.nativeVisibilityMechanismAvailable /\
  g.absoluteTemperatureOrEtaBAnchorStillRequired

theorem eq40_saha_supplies_visibility_but_not_absolute_epoch
    (g : Eq40SahaIonizationScalingGate)
    (hReady : eq40SahaIonizationReady g) :
    g.nativeVisibilityMechanismAvailable /\
      g.absoluteTemperatureOrEtaBAnchorStillRequired := by
  exact And.intro hReady.2.2.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.2.2.2

end P0EFTJanusEq40SahaIonizationScalingGate
end JanusFormal
