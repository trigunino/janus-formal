namespace JanusFormal
namespace P0EFTBAORedshiftRemapDiagnostic

set_option autoImplicit false

structure BAORedshiftRemapDiagnostic where
  spinBackgroundScreened : Prop
  radialRedshiftPowerScanned : Prop
  transverseRedshiftPowerScanned : Prop
  anisotropicRemapScored : Prop
  acceptableShapeFound : Prop
  remapGeometryDerived : Prop

def remapDiagnosticReady (d : BAORedshiftRemapDiagnostic) : Prop :=
  d.spinBackgroundScreened /\
  d.radialRedshiftPowerScanned /\
  d.transverseRedshiftPowerScanned /\
  d.anisotropicRemapScored

def remapNoFitReady (d : BAORedshiftRemapDiagnostic) : Prop :=
  remapDiagnosticReady d /\
  d.acceptableShapeFound /\
  d.remapGeometryDerived

theorem scan_closes_redshift_remap_diagnostic
    (d : BAORedshiftRemapDiagnostic)
    (hScreened : d.spinBackgroundScreened)
    (hRadial : d.radialRedshiftPowerScanned)
    (hTransverse : d.transverseRedshiftPowerScanned)
    (hScored : d.anisotropicRemapScored) :
    remapDiagnosticReady d := by
  exact And.intro hScreened
    (And.intro hRadial
      (And.intro hTransverse hScored))

theorem missing_remap_geometry_blocks_no_fit
    (d : BAORedshiftRemapDiagnostic)
    (hMissing : Not d.remapGeometryDerived) :
    Not (remapNoFitReady d) := by
  intro h
  exact hMissing h.right.right

end P0EFTBAORedshiftRemapDiagnostic
end JanusFormal
