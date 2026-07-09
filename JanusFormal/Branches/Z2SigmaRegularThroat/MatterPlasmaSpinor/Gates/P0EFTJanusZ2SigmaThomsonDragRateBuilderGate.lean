namespace JanusFormal
namespace P0EFTJanusZ2SigmaThomsonDragRateBuilderGate

set_option autoImplicit false

structure ThomsonDragRateBuilderGate where
  thomsonDragRateBuilderReady : Prop
  usesBaryonLoadingR : Prop
  requiresActiveFreeElectronDensity : Prop
  requiresActiveBaryonDensity : Prop
  requiresActivePhotonDensity : Prop
  requiresExplicitSigmaThomson : Prop
  requiresActiveH0Z2Sigma : Prop
  gammaDragOverH0BuilderReady : Prop
  gammaDragValuesReady : Prop
  gammaDragOverH0ValuesReady : Prop

def strictThomsonDragRateBuilderReady
    (g : ThomsonDragRateBuilderGate) : Prop :=
  g.thomsonDragRateBuilderReady /\
  g.usesBaryonLoadingR /\
  g.requiresActiveFreeElectronDensity /\
  g.requiresActiveBaryonDensity /\
  g.requiresActivePhotonDensity /\
  g.requiresExplicitSigmaThomson /\
  g.gammaDragOverH0BuilderReady /\
  g.requiresActiveH0Z2Sigma

theorem gamma_drag_values_require_active_electron_density
    (g : ThomsonDragRateBuilderGate)
    (hValues : g.gammaDragValuesReady)
    (hImplies : g.gammaDragValuesReady -> g.requiresActiveFreeElectronDensity) :
    g.requiresActiveFreeElectronDensity := by
  exact hImplies hValues

theorem gamma_drag_over_h0_values_require_active_h0
    (g : ThomsonDragRateBuilderGate)
    (hValues : g.gammaDragOverH0ValuesReady)
    (hImplies : g.gammaDragOverH0ValuesReady -> g.requiresActiveH0Z2Sigma) :
    g.requiresActiveH0Z2Sigma := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaThomsonDragRateBuilderGate
end JanusFormal
