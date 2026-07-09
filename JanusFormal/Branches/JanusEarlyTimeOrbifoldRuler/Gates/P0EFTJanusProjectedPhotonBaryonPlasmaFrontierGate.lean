namespace JanusFormal
namespace P0EFTJanusProjectedPhotonBaryonPlasmaFrontierGate

set_option autoImplicit false

structure ProjectedPhotonBaryonPlasmaFrontierGate where
  soundSpeedFormulaReady : Prop
  thomsonDragFormulaReady : Prop
  dragEpochSolverReady : Prop
  soundRulerIntegratorReady : Prop
  activeBaryonPhotonNormalizationsDerived : Prop
  activeIonizationThomsonNormalizationsDerived : Prop
  activePredragHubbleDerived : Prop
  noLCDMRdReuse : Prop
  noMockPlasmaInputs : Prop
  nativeRdEvaluated : Prop

def plasmaFrontierBlocked (g : ProjectedPhotonBaryonPlasmaFrontierGate) : Prop :=
  g.soundSpeedFormulaReady /\
  g.thomsonDragFormulaReady /\
  g.dragEpochSolverReady /\
  g.soundRulerIntegratorReady /\
  Not g.activeBaryonPhotonNormalizationsDerived /\
  Not g.activeIonizationThomsonNormalizationsDerived /\
  Not g.activePredragHubbleDerived /\
  g.noLCDMRdReuse /\
  g.noMockPlasmaInputs /\
  Not g.nativeRdEvaluated

theorem missing_active_plasma_and_hubble_blocks_native_rd
    (g : ProjectedPhotonBaryonPlasmaFrontierGate)
    (h : plasmaFrontierBlocked g) :
    Not g.nativeRdEvaluated := by
  exact h.2.2.2.2.2.2.2.2.2

end P0EFTJanusProjectedPhotonBaryonPlasmaFrontierGate
end JanusFormal
