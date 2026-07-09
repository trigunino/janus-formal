namespace JanusFormal
namespace P0EFTDESIBAOResidualDiagnostics

set_option autoImplicit false

structure DESIBAOResidualDiagnostics where
  baselineBAOShapeScored : Prop
  residualsGroupedByQuantity : Prop
  membraneSplitJunctionScanned : Prop
  splitJunctionRescuesShape : Prop
  acousticRulerOrRedshiftMapOpen : Prop

def diagnosticsReady (d : DESIBAOResidualDiagnostics) : Prop :=
  d.baselineBAOShapeScored /\
  d.residualsGroupedByQuantity /\
  d.membraneSplitJunctionScanned

def distanceFailureStillOpen (d : DESIBAOResidualDiagnostics) : Prop :=
  diagnosticsReady d /\
  Not d.splitJunctionRescuesShape /\
  d.acousticRulerOrRedshiftMapOpen

theorem grouped_residuals_and_split_scan_close_diagnostic_gate
    (d : DESIBAOResidualDiagnostics)
    (hBase : d.baselineBAOShapeScored)
    (hGrouped : d.residualsGroupedByQuantity)
    (hSplit : d.membraneSplitJunctionScanned) :
    diagnosticsReady d := by
  exact And.intro hBase (And.intro hGrouped hSplit)

theorem failed_split_scan_keeps_ruler_or_redshift_open
    (d : DESIBAOResidualDiagnostics)
    (hReady : diagnosticsReady d)
    (hNoRescue : Not d.splitJunctionRescuesShape)
    (hOpen : d.acousticRulerOrRedshiftMapOpen) :
    distanceFailureStillOpen d := by
  exact And.intro hReady (And.intro hNoRescue hOpen)

end P0EFTDESIBAOResidualDiagnostics
end JanusFormal
