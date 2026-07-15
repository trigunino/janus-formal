import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWOscillationGate

namespace JanusFormal
namespace P0EFTJanusGWSourceDetectorInterface

set_option autoImplicit false

/-- Minimal linear source -> eigenmodes -> propagation -> detector pipeline. -/
structure SourceDetectorPipeline where
  sourceDiagonal : ℝ
  sourceRelative : ℝ
  propagateDiagonal : ℝ
  propagateRelative : ℝ
  detectorDiagonal : ℝ
  detectorRelative : ℝ

def detectedAmplitude (p : SourceDetectorPipeline) : ℝ :=
  p.detectorDiagonal * p.propagateDiagonal * p.sourceDiagonal +
    p.detectorRelative * p.propagateRelative * p.sourceRelative

/-- In the GR limit only the common diagonal channel is sourced and detected. -/
theorem gr_limit_pipeline
    (source propagation detector : ℝ) :
    detectedAmplitude {
      sourceDiagonal := source
      sourceRelative := 0
      propagateDiagonal := propagation
      propagateRelative := 0
      detectorDiagonal := detector
      detectorRelative := 0 } =
      detector * propagation * source := by
  simp [detectedAmplitude]

/-- An unsourced relative mode cannot affect the detector even if it has a
nontrivial propagation factor. -/
theorem unsourced_relative_channel_decouples
    (source propagationDiagonal propagationRelative detectorDiagonal
      detectorRelative : ℝ) :
    detectedAmplitude {
      sourceDiagonal := source
      sourceRelative := 0
      propagateDiagonal := propagationDiagonal
      propagateRelative := propagationRelative
      detectorDiagonal := detectorDiagonal
      detectorRelative := detectorRelative } =
      detectorDiagonal * propagationDiagonal * source := by
  simp [detectedAmplitude]

structure GW04Inputs where
  sourceProjectionDerivedFromP : Prop
  propagationKernelDerived : Prop
  detectorProjectionDerivedFromP : Prop
  waveformNormalizationDerived : Prop

def physicalGW04Closed (s : GW04Inputs) : Prop :=
  s.sourceProjectionDerivedFromP ∧
  s.propagationKernelDerived ∧
  s.detectorProjectionDerivedFromP ∧
  s.waveformNormalizationDerived

end P0EFTJanusGWSourceDetectorInterface
end JanusFormal
