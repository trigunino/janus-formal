namespace JanusFormal
namespace P0EFTDESIDHInverseHubbleDiagnostic

set_option autoImplicit false

structure DESIDHInverseHubbleDiagnostic where
  postScreeningBackgroundUsed : Prop
  desiRadialDHRowsExtracted : Prop
  requiredHubbleMultiplierComputed : Prop
  constantRescaleSufficient : Prop
  redshiftDependentCorrectionNeeded : Prop

def inverseHubbleDiagnosticReady (d : DESIDHInverseHubbleDiagnostic) : Prop :=
  d.postScreeningBackgroundUsed /\
  d.desiRadialDHRowsExtracted /\
  d.requiredHubbleMultiplierComputed

def radialCorrectionTargetReady (d : DESIDHInverseHubbleDiagnostic) : Prop :=
  inverseHubbleDiagnosticReady d /\
  Not d.constantRescaleSufficient /\
  d.redshiftDependentCorrectionNeeded

theorem inverse_hubble_rows_close_diagnostic_gate
    (d : DESIDHInverseHubbleDiagnostic)
    (hPost : d.postScreeningBackgroundUsed)
    (hRows : d.desiRadialDHRowsExtracted)
    (hMultiplier : d.requiredHubbleMultiplierComputed) :
    inverseHubbleDiagnosticReady d := by
  exact And.intro hPost (And.intro hRows hMultiplier)

theorem nonconstant_multiplier_targets_redshift_correction
    (d : DESIDHInverseHubbleDiagnostic)
    (hReady : inverseHubbleDiagnosticReady d)
    (hNotConstant : Not d.constantRescaleSufficient)
    (hNeeded : d.redshiftDependentCorrectionNeeded) :
    radialCorrectionTargetReady d := by
  exact And.intro hReady (And.intro hNotConstant hNeeded)

end P0EFTDESIDHInverseHubbleDiagnostic
end JanusFormal
