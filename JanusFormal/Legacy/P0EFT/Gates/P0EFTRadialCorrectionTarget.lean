namespace JanusFormal
namespace P0EFTRadialCorrectionTarget

set_option autoImplicit false

structure RadialCorrectionTarget where
  inverseDHMultiplierComputed : Prop
  radialCorrectionAppliedToBAOShape : Prop
  acceptableBAOShapeFound : Prop
  radialCorrectionGeometryDerived : Prop

def radialCorrectionDiagnosticReady (r : RadialCorrectionTarget) : Prop :=
  r.inverseDHMultiplierComputed /\
  r.radialCorrectionAppliedToBAOShape

def radialCorrectionNoFitReady (r : RadialCorrectionTarget) : Prop :=
  radialCorrectionDiagnosticReady r /\
  r.acceptableBAOShapeFound /\
  r.radialCorrectionGeometryDerived

theorem inverse_multiplier_supplies_radial_target
    (r : RadialCorrectionTarget)
    (hInverse : r.inverseDHMultiplierComputed)
    (hApplied : r.radialCorrectionAppliedToBAOShape) :
    radialCorrectionDiagnosticReady r := by
  exact And.intro hInverse hApplied

theorem missing_radial_geometry_blocks_no_fit
    (r : RadialCorrectionTarget)
    (hMissing : Not r.radialCorrectionGeometryDerived) :
    Not (radialCorrectionNoFitReady r) := by
  intro h
  exact hMissing h.right.right

end P0EFTRadialCorrectionTarget
end JanusFormal
