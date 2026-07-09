namespace JanusFormal
namespace P0EFTJanusZ2SigmaDimensionlessCurvatureScaleInputWriterGate

set_option autoImplicit false

structure DimensionlessCurvatureScaleInputWriterGate where
  activeCoreZ2TunnelSigma : Prop
  inputManifestAvailable : Prop
  dimensionlessCurvatureScaleInputWritten : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def dimensionlessCurvatureScaleInputClosed
    (g : DimensionlessCurvatureScaleInputWriterGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.inputManifestAvailable /\
  g.dimensionlessCurvatureScaleInputWritten /\
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed /\
  g.gatePassed

theorem dimensionless_scale_writer_forbids_fitted_curvature
    (g : DimensionlessCurvatureScaleInputWriterGate)
    (hClosed : dimensionlessCurvatureScaleInputClosed g) :
    Not g.observationalH0FitUsed /\ Not g.observationalCurvatureFitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, hNoH0, hNoCurv, _⟩
  exact ⟨hNoH0, hNoCurv⟩

end P0EFTJanusZ2SigmaDimensionlessCurvatureScaleInputWriterGate
end JanusFormal
