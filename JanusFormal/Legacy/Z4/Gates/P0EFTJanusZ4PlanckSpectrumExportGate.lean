import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckAdapterContract

namespace JanusFormal
namespace P0EFTJanusZ4PlanckSpectrumExportGate

set_option autoImplicit false

structure PlanckSpectrumExportGate where
  requiredColumnsPresent : Prop
  ellGridStrictlyIncreasing : Prop
  spectraFinite : Prop
  spectraUnitsDeclared : Prop
  covarianceInputDeclared : Prop
  planckLikelihoodExecuted : Prop

def spectrumExportGateReady (p : PlanckSpectrumExportGate) : Prop :=
  p.requiredColumnsPresent /\
  p.ellGridStrictlyIncreasing /\
  p.spectraFinite /\
  p.spectraUnitsDeclared /\
  p.covarianceInputDeclared

def planckAdapterExecutionReady (p : PlanckSpectrumExportGate) : Prop :=
  spectrumExportGateReady p /\
  p.planckLikelihoodExecuted

theorem spectrum_gate_requires_finite_spectra
    (p : PlanckSpectrumExportGate)
    (h : spectrumExportGateReady p) :
    p.spectraFinite := by
  exact h.right.right.left

theorem spectrum_gate_does_not_execute_likelihood
    (p : PlanckSpectrumExportGate)
    (_h : spectrumExportGateReady p)
    (hMissing : Not p.planckLikelihoodExecuted) :
    Not (planckAdapterExecutionReady p) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4PlanckSpectrumExportGate
end JanusFormal
