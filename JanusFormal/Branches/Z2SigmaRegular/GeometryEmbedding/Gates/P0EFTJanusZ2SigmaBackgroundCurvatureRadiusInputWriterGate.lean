namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundCurvatureRadiusInputWriterGate

set_option autoImplicit false

structure BackgroundCurvatureRadiusInputWriterGate where
  activeCoreZ2TunnelSigma : Prop
  inputManifestAvailable : Prop
  backgroundCurvatureRadiusInputWritten : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  requiresActiveCurvatureRadiusScaleNormalization : Prop
  requiresActiveEmbeddingOrThroatRadiusScale : Prop
  dimensionlessH0ROverCInsufficientForRCurv : Prop
  gatePassed : Prop

def curvatureRadiusInputClosed
    (g : BackgroundCurvatureRadiusInputWriterGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.inputManifestAvailable /\
  g.backgroundCurvatureRadiusInputWritten /\
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed /\
  g.requiresActiveCurvatureRadiusScaleNormalization /\
  g.requiresActiveEmbeddingOrThroatRadiusScale /\
  g.dimensionlessH0ROverCInsufficientForRCurv /\
  g.gatePassed

theorem curvature_radius_writer_forbids_fitted_curvature
    (g : BackgroundCurvatureRadiusInputWriterGate)
    (hClosed : curvatureRadiusInputClosed g) :
    Not g.observationalH0FitUsed /\ Not g.observationalCurvatureFitUsed := by
  exact ⟨hClosed.2.2.2.2.2.1, hClosed.2.2.2.2.2.2.1⟩

theorem curvature_radius_requires_dimensional_embedding_scale
    (g : BackgroundCurvatureRadiusInputWriterGate)
    (hClosed : curvatureRadiusInputClosed g) :
    g.requiresActiveCurvatureRadiusScaleNormalization /\
      g.requiresActiveEmbeddingOrThroatRadiusScale /\
      g.dimensionlessH0ROverCInsufficientForRCurv := by
  exact ⟨hClosed.2.2.2.2.2.2.2.1,
    hClosed.2.2.2.2.2.2.2.2.1,
    hClosed.2.2.2.2.2.2.2.2.2.1⟩

end P0EFTJanusZ2SigmaBackgroundCurvatureRadiusInputWriterGate
end JanusFormal
