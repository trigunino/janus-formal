import JanusFormal.P0EFTJanusZ2SigmaActiveCurvatureSignGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaScaleFreeOmegaKFromCurvatureScaleGate

set_option autoImplicit false

structure ScaleFreeOmegaKFromCurvatureScaleGate where
  activeCoreZ2Sigma : Prop
  curvatureSignInputAvailable : Prop
  dimensionlessCurvatureScaleInputAvailable : Prop
  omegaKFormulaReady : Prop
  omegaKFormulaUsesH0RcurvOverC : Prop
  noCompressedPlanckLCDMBackground : Prop
  noArchivedZ4Background : Prop
  noObservationalH0Fit : Prop
  noObservationalCurvatureFit : Prop
  scaleFreeOmegaKWritten : Prop
  gatePassed : Prop

def scaleFreeOmegaKPolicyClosed
    (g : ScaleFreeOmegaKFromCurvatureScaleGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.curvatureSignInputAvailable /\
  g.dimensionlessCurvatureScaleInputAvailable /\
  g.omegaKFormulaReady /\
  g.omegaKFormulaUsesH0RcurvOverC /\
  g.noCompressedPlanckLCDMBackground /\
  g.noArchivedZ4Background /\
  g.noObservationalH0Fit /\
  g.noObservationalCurvatureFit

theorem gate_pass_requires_scale_free_omega_k_manifest
    (g : ScaleFreeOmegaKFromCurvatureScaleGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.scaleFreeOmegaKWritten) :
    g.scaleFreeOmegaKWritten := by
  exact hImplies _hGate

theorem scale_free_path_requires_dimensionless_curvature_scale
    (g : ScaleFreeOmegaKFromCurvatureScaleGate)
    (h : scaleFreeOmegaKPolicyClosed g) :
    g.dimensionlessCurvatureScaleInputAvailable := by
  exact h.2.2.1

end P0EFTJanusZ2SigmaScaleFreeOmegaKFromCurvatureScaleGate
end JanusFormal
