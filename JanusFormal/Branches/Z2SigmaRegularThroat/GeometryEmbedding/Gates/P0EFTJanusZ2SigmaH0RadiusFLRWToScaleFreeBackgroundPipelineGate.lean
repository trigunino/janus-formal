namespace JanusFormal
namespace P0EFTJanusZ2SigmaH0RadiusFLRWToScaleFreeBackgroundPipelineGate

set_option autoImplicit false

structure H0RadiusFLRWToScaleFreeBackgroundPipelineGate where
  activeCoreZ2TunnelSigma : Prop
  activeH0InputValid : Prop
  activeCurvatureRadiusInputValid : Prop
  activeCurvatureSignInputValid : Prop
  activeFLRWComponentsValid : Prop
  omegaKPipelinePassed : Prop
  backgroundPrimitivePassed : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def noLegacyBackgroundPipelineInputs
    (g : H0RadiusFLRWToScaleFreeBackgroundPipelineGate) : Prop :=
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed

def scaleFreeBackgroundReady
    (g : H0RadiusFLRWToScaleFreeBackgroundPipelineGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.activeH0InputValid /\
  g.activeCurvatureRadiusInputValid /\
  g.activeCurvatureSignInputValid /\
  g.activeFLRWComponentsValid /\
  g.omegaKPipelinePassed /\
  g.backgroundPrimitivePassed /\
  noLegacyBackgroundPipelineInputs g

theorem gate_pass_requires_scale_free_background_chain
    (g : H0RadiusFLRWToScaleFreeBackgroundPipelineGate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> scaleFreeBackgroundReady g) :
    scaleFreeBackgroundReady g := by
  exact hImplies hPass

end P0EFTJanusZ2SigmaH0RadiusFLRWToScaleFreeBackgroundPipelineGate
end JanusFormal
