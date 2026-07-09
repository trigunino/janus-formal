import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4PlanckLikelihoodDryRunTarget

namespace JanusFormal
namespace P0EFTJanusZ4PlanckAdapterReadyClosure

set_option autoImplicit false

structure PlanckAdapterReadyClosure where
  spectrumColumnsReady : Prop
  ellGridReady : Prop
  spectraFinite : Prop
  covarianceContractReady : Prop
  dryRunChi2Finite : Prop
  reportExported : Prop
  officialLikelihoodNotClaimed : Prop

def planckAdapterReadyClosureReady (p : PlanckAdapterReadyClosure) : Prop :=
  p.spectrumColumnsReady /\
  p.ellGridReady /\
  p.spectraFinite /\
  p.covarianceContractReady /\
  p.dryRunChi2Finite /\
  p.reportExported /\
  p.officialLikelihoodNotClaimed

theorem adapter_ready_gives_finite_spectra
    (p : PlanckAdapterReadyClosure)
    (h : planckAdapterReadyClosureReady p) :
    p.spectraFinite := by
  exact h.right.right.left

theorem adapter_ready_does_not_claim_official_likelihood
    (p : PlanckAdapterReadyClosure)
    (h : planckAdapterReadyClosureReady p) :
    p.officialLikelihoodNotClaimed := by
  exact h.right.right.right.right.right.right

end P0EFTJanusZ4PlanckAdapterReadyClosure
end JanusFormal
