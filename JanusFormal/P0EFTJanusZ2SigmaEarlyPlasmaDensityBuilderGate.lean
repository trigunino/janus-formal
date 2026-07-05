namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaDensityBuilderGate

set_option autoImplicit false

structure EarlyPlasmaDensityBuilderGate where
  baryonDensityBuilderReady : Prop
  photonDensityBuilderReady : Prop
  freeElectronDensityBuilderReady : Prop
  requiresActiveBaryonNormalization : Prop
  requiresActivePhotonNormalization : Prop
  requiresActiveBaryonNumberDensity : Prop
  requiresActiveIonizationFraction : Prop
  earlyPlasmaDensityValuesReady : Prop

def strictEarlyPlasmaDensityBuilderReady
    (g : EarlyPlasmaDensityBuilderGate) : Prop :=
  g.baryonDensityBuilderReady /\
  g.photonDensityBuilderReady /\
  g.freeElectronDensityBuilderReady /\
  g.requiresActiveBaryonNormalization /\
  g.requiresActivePhotonNormalization /\
  g.requiresActiveBaryonNumberDensity /\
  g.requiresActiveIonizationFraction

theorem density_values_require_active_normalizations
    (g : EarlyPlasmaDensityBuilderGate)
    (hValues : g.earlyPlasmaDensityValuesReady)
    (hImplies :
      g.earlyPlasmaDensityValuesReady ->
        g.requiresActiveBaryonNormalization /\ g.requiresActivePhotonNormalization) :
    g.requiresActiveBaryonNormalization /\ g.requiresActivePhotonNormalization := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaEarlyPlasmaDensityBuilderGate
end JanusFormal
