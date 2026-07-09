namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundCurvatureNormalizationFromBranchGate

set_option autoImplicit false

structure BackgroundCurvatureNormalizationFromBranchGate where
  activeCoreZ2Sigma : Prop
  activeFLRWSpatialMetricBranchValuesReady : Prop
  computesOmegaKFromKRcurvH0 : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  usesObservationalH0Fit : Prop
  backgroundCurvatureNormalizationInputWritten : Prop
  gatePassed : Prop

def curvatureNormalizationTransportPolicyClosed
    (g : BackgroundCurvatureNormalizationFromBranchGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.computesOmegaKFromKRcurvH0 /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit /\
  Not g.usesObservationalH0Fit

theorem gate_pass_requires_written_normalization_input
    (g : BackgroundCurvatureNormalizationFromBranchGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.backgroundCurvatureNormalizationInputWritten) :
    g.backgroundCurvatureNormalizationInputWritten := by
  exact hImplies _hGate

theorem gate_pass_requires_active_branch_values
    (g : BackgroundCurvatureNormalizationFromBranchGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.activeFLRWSpatialMetricBranchValuesReady) :
    g.activeFLRWSpatialMetricBranchValuesReady := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaBackgroundCurvatureNormalizationFromBranchGate
end JanusFormal
