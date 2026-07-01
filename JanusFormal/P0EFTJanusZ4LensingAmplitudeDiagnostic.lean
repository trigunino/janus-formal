import JanusFormal.P0EFTJanusZ4OfficialPlanckGate

namespace JanusFormal
namespace P0EFTJanusZ4LensingAmplitudeDiagnostic

set_option autoImplicit false

structure LensingAmplitudeDiagnostic where
  nativeZ4SpectraUsed : Prop
  officialPlanckLensingExecuted : Prop
  compressedLCDMParametersNotUsed : Prop
  amplitudeScanExecuted : Prop
  amplitudeOnlySufficient : Prop

def lensingAmplitudeDiagnosticReady (d : LensingAmplitudeDiagnostic) : Prop :=
  d.nativeZ4SpectraUsed /\
  d.officialPlanckLensingExecuted /\
  d.compressedLCDMParametersNotUsed /\
  d.amplitudeScanExecuted

def lensingProjectionStillRequired (d : LensingAmplitudeDiagnostic) : Prop :=
  lensingAmplitudeDiagnosticReady d /\ Not d.amplitudeOnlySufficient

theorem failed_amplitude_scan_requires_projection_kernel
    (d : LensingAmplitudeDiagnostic)
    (h : lensingProjectionStillRequired d) :
    Not d.amplitudeOnlySufficient := by
  exact h.right

end P0EFTJanusZ4LensingAmplitudeDiagnostic
end JanusFormal
