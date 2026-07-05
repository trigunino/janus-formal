namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaNormalizationBuilderGate

set_option autoImplicit false

structure EarlyPlasmaNormalizationBuilderGate where
  baryonNumberDensityBuilderReady : Prop
  baryonMassDensityFromNumberBuilderReady : Prop
  conservedPhotonTemperatureBuilderReady : Prop
  blackbodyPhotonDensityBuilderReady : Prop
  freeElectronNormalizationChainReady : Prop
  requiresActiveBaryonMassDensity : Prop
  requiresActiveBaryonNumberDensity : Prop
  requiresExplicitBaryonMass : Prop
  requiresActivePhotonTemperatureNormalization : Prop
  requiresActivePhotonTemperature : Prop
  requiresExplicitRadiationConstant : Prop
  requiresActiveIonizationFraction : Prop
  earlyPlasmaNormalizationValuesReady : Prop

def strictEarlyPlasmaNormalizationBuilderReady
    (g : EarlyPlasmaNormalizationBuilderGate) : Prop :=
  g.baryonNumberDensityBuilderReady /\
  g.baryonMassDensityFromNumberBuilderReady /\
  g.conservedPhotonTemperatureBuilderReady /\
  g.blackbodyPhotonDensityBuilderReady /\
  g.freeElectronNormalizationChainReady /\
  g.requiresActiveBaryonMassDensity /\
  g.requiresActiveBaryonNumberDensity /\
  g.requiresExplicitBaryonMass /\
  g.requiresActivePhotonTemperatureNormalization /\
  g.requiresActivePhotonTemperature /\
  g.requiresExplicitRadiationConstant /\
  g.requiresActiveIonizationFraction

theorem normalization_values_require_active_temperature
    (g : EarlyPlasmaNormalizationBuilderGate)
    (hValues : g.earlyPlasmaNormalizationValuesReady)
    (hImplies :
      g.earlyPlasmaNormalizationValuesReady -> g.requiresActivePhotonTemperature) :
    g.requiresActivePhotonTemperature := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaEarlyPlasmaNormalizationBuilderGate
end JanusFormal
