namespace JanusFormal
namespace P0EFTJanusZ2SigmaDimensionlessCurvatureScaleFromH0RadiusGate

set_option autoImplicit false

structure DimensionlessCurvatureScaleFromH0RadiusGate where
  activeCoreZ2TunnelSigma : Prop
  h0InputAvailable : Prop
  curvatureRadiusInputAvailable : Prop
  dimensionlessCurvatureScaleNormalizationWritten : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def scaleFreeNormalizationClosed
    (g : DimensionlessCurvatureScaleFromH0RadiusGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.h0InputAvailable /\
  g.curvatureRadiusInputAvailable /\
  g.dimensionlessCurvatureScaleNormalizationWritten /\
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed /\
  g.gatePassed

theorem scale_free_normalization_forbids_compressed_or_fitted_inputs
    (g : DimensionlessCurvatureScaleFromH0RadiusGate)
    (hClosed : scaleFreeNormalizationClosed g) :
    Not g.compressedPlanckLCDMBackgroundUsed /\
    Not g.archivedZ4BackgroundUsed /\
    Not g.observationalH0FitUsed /\
    Not g.observationalCurvatureFitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, hNoPlanck, hNoZ4, hNoH0, hNoCurv, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0, hNoCurv⟩

end P0EFTJanusZ2SigmaDimensionlessCurvatureScaleFromH0RadiusGate
end JanusFormal
