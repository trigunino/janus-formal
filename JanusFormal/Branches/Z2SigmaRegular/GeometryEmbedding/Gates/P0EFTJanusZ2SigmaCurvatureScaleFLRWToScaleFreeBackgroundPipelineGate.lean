namespace JanusFormal
namespace P0EFTJanusZ2SigmaCurvatureScaleFLRWToScaleFreeBackgroundPipelineGate

set_option autoImplicit false

structure CurvatureScaleFLRWToScaleFreeBackgroundPipelineGate where
  activeCoreZ2TunnelSigma : Prop
  curvatureSignInputValid : Prop
  dimensionlessCurvatureScaleInputValid : Prop
  activeFLRWComponentsValid : Prop
  omegaKFromCurvatureScalePassed : Prop
  backgroundPrimitivePassed : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def noLegacyScaleFreeBackgroundInputs
    (g : CurvatureScaleFLRWToScaleFreeBackgroundPipelineGate) : Prop :=
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed

def scaleFreeBackgroundReady
    (g : CurvatureScaleFLRWToScaleFreeBackgroundPipelineGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.curvatureSignInputValid /\
  g.dimensionlessCurvatureScaleInputValid /\
  g.activeFLRWComponentsValid /\
  g.omegaKFromCurvatureScalePassed /\
  g.backgroundPrimitivePassed /\
  noLegacyScaleFreeBackgroundInputs g

theorem gate_pass_requires_scale_free_curvature_background_chain
    (g : CurvatureScaleFLRWToScaleFreeBackgroundPipelineGate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> scaleFreeBackgroundReady g) :
    scaleFreeBackgroundReady g := by
  exact hImplies hPass

end P0EFTJanusZ2SigmaCurvatureScaleFLRWToScaleFreeBackgroundPipelineGate
end JanusFormal
