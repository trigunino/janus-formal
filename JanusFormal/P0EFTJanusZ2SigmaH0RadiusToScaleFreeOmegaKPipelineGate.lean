namespace JanusFormal
namespace P0EFTJanusZ2SigmaH0RadiusToScaleFreeOmegaKPipelineGate

set_option autoImplicit false

structure H0RadiusToScaleFreeOmegaKPipelineGate where
  activeCoreZ2TunnelSigma : Prop
  activeH0Available : Prop
  activeCurvatureRadiusAvailable : Prop
  activeCurvatureSignAvailable : Prop
  dimensionlessScaleWritten : Prop
  scaleInputWriterPassed : Prop
  scaleFreeOmegaKWritten : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def omegaKPipelineClosed
    (g : H0RadiusToScaleFreeOmegaKPipelineGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.activeH0Available /\
  g.activeCurvatureRadiusAvailable /\
  g.activeCurvatureSignAvailable /\
  g.dimensionlessScaleWritten /\
  g.scaleInputWriterPassed /\
  g.scaleFreeOmegaKWritten /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed /\
  g.gatePassed

theorem closed_forbids_compressed_or_archived_inputs
    (g : H0RadiusToScaleFreeOmegaKPipelineGate)
    (hClosed : omegaKPipelineClosed g) :
    Not g.compressedPlanckLCDMUsed /\
    Not g.archivedZ4Used /\
    Not g.observationalH0FitUsed /\
    Not g.observationalCurvatureFitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, hNoCurv, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0, hNoCurv⟩

end P0EFTJanusZ2SigmaH0RadiusToScaleFreeOmegaKPipelineGate
end JanusFormal
