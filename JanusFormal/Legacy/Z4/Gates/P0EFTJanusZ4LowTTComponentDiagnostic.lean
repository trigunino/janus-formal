import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4OfficialPlanckGate

namespace JanusFormal
namespace P0EFTJanusZ4LowTTComponentDiagnostic

set_option autoImplicit false

structure LowTTComponentDiagnostic where
  nativeZ4SolverUsed : Prop
  compressedLCDMParametersNotUsed : Prop
  officialPlanckLikelihoodNotClaimed : Prop
  officialLowTTRejectedElsewhere : Prop
  sachsWolfeComponentExposed : Prop
  dopplerComponentExposed : Prop
  integratedSachsWolfeComponentExposed : Prop
  componentInterferenceExposed : Prop

def lowTTComponentDiagnosticReady (d : LowTTComponentDiagnostic) : Prop :=
  d.nativeZ4SolverUsed /\
  d.compressedLCDMParametersNotUsed /\
  d.officialPlanckLikelihoodNotClaimed /\
  d.officialLowTTRejectedElsewhere /\
  d.sachsWolfeComponentExposed /\
  d.dopplerComponentExposed /\
  d.integratedSachsWolfeComponentExposed /\
  d.componentInterferenceExposed

theorem lowtt_component_diagnostic_is_not_official_gate
    (d : LowTTComponentDiagnostic)
    (h : lowTTComponentDiagnosticReady d) :
    d.officialPlanckLikelihoodNotClaimed := by
  exact h.right.right.left

theorem lowtt_component_diagnostic_exposes_all_sources
    (d : LowTTComponentDiagnostic)
    (h : lowTTComponentDiagnosticReady d) :
    d.sachsWolfeComponentExposed /\
    d.dopplerComponentExposed /\
    d.integratedSachsWolfeComponentExposed /\
    d.componentInterferenceExposed := by
  exact ⟨h.right.right.right.right.left,
    h.right.right.right.right.right.left,
    h.right.right.right.right.right.right.left,
    h.right.right.right.right.right.right.right⟩

end P0EFTJanusZ4LowTTComponentDiagnostic
end JanusFormal
