import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ShapeDiagnostic

namespace JanusFormal
namespace P0EFTJanusZ4PeakDampingDiagnostic

set_option autoImplicit false

structure PeakDampingDiagnostic where
  nativeZ4ProviderUsed : Prop
  compressedLCDMParametersNotUsed : Prop
  officialPlanckLikelihoodNotClaimed : Prop
  ttPeakPhaseExposed : Prop
  teZeroPhaseExposed : Prop
  eePeakPhaseExposed : Prop
  ttDampingSlopeExposed : Prop
  cmbEnginePhysicallyClosedNotClaimed : Prop

def peakDampingDiagnosticReady (d : PeakDampingDiagnostic) : Prop :=
  d.nativeZ4ProviderUsed /\
  d.compressedLCDMParametersNotUsed /\
  d.officialPlanckLikelihoodNotClaimed /\
  d.ttPeakPhaseExposed /\
  d.teZeroPhaseExposed /\
  d.eePeakPhaseExposed /\
  d.ttDampingSlopeExposed /\
  d.cmbEnginePhysicallyClosedNotClaimed

theorem peak_damping_diagnostic_is_not_cmb_closure
    (d : PeakDampingDiagnostic)
    (h : peakDampingDiagnosticReady d) :
    d.cmbEnginePhysicallyClosedNotClaimed := by
  exact h.right.right.right.right.right.right.right

theorem peak_damping_diagnostic_exposes_acoustic_obligations
    (d : PeakDampingDiagnostic)
    (h : peakDampingDiagnosticReady d) :
    d.ttPeakPhaseExposed /\ d.teZeroPhaseExposed /\ d.ttDampingSlopeExposed := by
  exact âŸ¨h.right.right.right.left, h.right.right.right.right.left, h.right.right.right.right.right.right.leftâŸ©

end P0EFTJanusZ4PeakDampingDiagnostic
end JanusFormal
