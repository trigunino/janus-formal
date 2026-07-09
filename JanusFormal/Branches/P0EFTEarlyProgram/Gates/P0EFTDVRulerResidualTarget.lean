namespace JanusFormal
namespace P0EFTDVRulerResidualTarget

set_option autoImplicit false

structure DVRulerResidualTarget where
  spinBackgroundScreened : Prop
  radialCorrectionTargetApplied : Prop
  dvRulerFactorScanned : Prop
  acceptableBAOShapeFound : Prop
  dvRulerGeometryDerived : Prop

def dvRulerDiagnosticReady (d : DVRulerResidualTarget) : Prop :=
  d.spinBackgroundScreened /\
  d.radialCorrectionTargetApplied /\
  d.dvRulerFactorScanned

def dvRulerNoFitReady (d : DVRulerResidualTarget) : Prop :=
  dvRulerDiagnosticReady d /\
  d.acceptableBAOShapeFound /\
  d.dvRulerGeometryDerived

theorem dv_ruler_scan_closes_diagnostic_gate
    (d : DVRulerResidualTarget)
    (hSpin : d.spinBackgroundScreened)
    (hRadial : d.radialCorrectionTargetApplied)
    (hScan : d.dvRulerFactorScanned) :
    dvRulerDiagnosticReady d := by
  exact And.intro hSpin (And.intro hRadial hScan)

theorem missing_dv_ruler_geometry_blocks_no_fit
    (d : DVRulerResidualTarget)
    (hMissing : Not d.dvRulerGeometryDerived) :
    Not (dvRulerNoFitReady d) := by
  intro h
  exact hMissing h.right.right

end P0EFTDVRulerResidualTarget
end JanusFormal
