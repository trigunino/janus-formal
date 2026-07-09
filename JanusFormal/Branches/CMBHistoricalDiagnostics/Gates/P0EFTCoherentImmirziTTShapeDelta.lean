namespace JanusFormal
namespace P0EFTCoherentImmirziTTShapeDelta

set_option autoImplicit false

structure CoherentImmirziTTShapeDelta where
  activeNeutralTTCompared : Prop
  peakShiftMeasured : Prop
  dampingRatioMeasured : Prop
  highLResidualExplained : Prop

def ttShapeDiagnosticReady (d : CoherentImmirziTTShapeDelta) : Prop :=
  d.activeNeutralTTCompared /\ d.peakShiftMeasured /\ d.dampingRatioMeasured

def highLClosureReady (d : CoherentImmirziTTShapeDelta) : Prop :=
  ttShapeDiagnosticReady d /\ d.highLResidualExplained

theorem diagnostic_without_explanation_blocks_high_l_closure
    (d : CoherentImmirziTTShapeDelta)
    (_hDiag : ttShapeDiagnosticReady d)
    (hMissing : Not d.highLResidualExplained) :
    Not (highLClosureReady d) := by
  intro h
  exact hMissing h.right

end P0EFTCoherentImmirziTTShapeDelta
end JanusFormal
