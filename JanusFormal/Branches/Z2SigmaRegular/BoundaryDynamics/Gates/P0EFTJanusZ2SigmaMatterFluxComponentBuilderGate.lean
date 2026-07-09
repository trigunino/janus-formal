namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxComponentBuilderGate

set_option autoImplicit false

structure MatterFluxComponentBuilderGate where
  transparentFluxComponentBuilderReady : Prop
  requiresActiveSigmaTransparencyDerived : Prop
  matterFluxZeroWithoutTransparencyForbidden : Prop
  matterFluxRhoPValuesReady : Prop

def transparentMatterFluxBuilderReady
    (g : MatterFluxComponentBuilderGate) : Prop :=
  g.transparentFluxComponentBuilderReady /\
  g.requiresActiveSigmaTransparencyDerived /\
  g.matterFluxZeroWithoutTransparencyForbidden

theorem zero_flux_values_require_transparency_guard
    (g : MatterFluxComponentBuilderGate)
    (hValues : g.matterFluxRhoPValuesReady)
    (hImplies :
      g.matterFluxRhoPValuesReady -> g.requiresActiveSigmaTransparencyDerived) :
    g.requiresActiveSigmaTransparencyDerived := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaMatterFluxComponentBuilderGate
end JanusFormal
