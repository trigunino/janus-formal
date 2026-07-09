namespace JanusFormal
namespace P0EFTJanusZ2SigmaDimensionlessCurvatureScaleFromBranchGate

set_option autoImplicit false

structure DimensionlessCurvatureScaleFromBranchGate where
  activeCoreZ2TunnelSigma : Prop
  curvatureBranchInputAvailable : Prop
  curvatureBranchAssemblerPassed : Prop
  dimensionlessCurvatureScaleNormalizationWritten : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def scaleFreeBranchNormalizationClosed
    (g : DimensionlessCurvatureScaleFromBranchGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.curvatureBranchInputAvailable /\
  g.dimensionlessCurvatureScaleNormalizationWritten /\
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed /\
  g.gatePassed

theorem branch_scale_normalization_forbids_compressed_or_fitted_inputs
    (g : DimensionlessCurvatureScaleFromBranchGate)
    (hClosed : scaleFreeBranchNormalizationClosed g) :
    Not g.compressedPlanckLCDMBackgroundUsed /\
    Not g.archivedZ4BackgroundUsed /\
    Not g.observationalH0FitUsed /\
    Not g.observationalCurvatureFitUsed := by
  rcases hClosed with
    ⟨_, _, _, hNoPlanck, hNoZ4, hNoH0, hNoCurv, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0, hNoCurv⟩

theorem branch_scale_normalization_requires_branch_input
    (g : DimensionlessCurvatureScaleFromBranchGate)
    (hClosed : scaleFreeBranchNormalizationClosed g) :
    g.curvatureBranchInputAvailable := by
  exact hClosed.2.1

end P0EFTJanusZ2SigmaDimensionlessCurvatureScaleFromBranchGate
end JanusFormal
