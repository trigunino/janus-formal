import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4CMBSpectrumAssemblyTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckSpectrumExportGate

namespace JanusFormal
namespace P0EFTJanusZ4PlanckLikelihoodDryRunTarget

set_option autoImplicit false

structure PlanckLikelihoodDryRunTarget where
  residualVectorDeclared : Prop
  covarianceDiagonalPositive : Prop
  finiteChi2Produced : Prop
  spectraAdapterInputUsed : Prop
  dryRunReportExported : Prop
  officialPlanckLikelihoodExecuted : Prop

def planckLikelihoodDryRunReady (p : PlanckLikelihoodDryRunTarget) : Prop :=
  p.residualVectorDeclared /\
  p.covarianceDiagonalPositive /\
  p.finiteChi2Produced /\
  p.spectraAdapterInputUsed /\
  p.dryRunReportExported

def planckLikelihoodPhysicalReady (p : PlanckLikelihoodDryRunTarget) : Prop :=
  planckLikelihoodDryRunReady p /\
  p.officialPlanckLikelihoodExecuted

theorem dry_run_requires_finite_chi2
    (p : PlanckLikelihoodDryRunTarget)
    (h : planckLikelihoodDryRunReady p) :
    p.finiteChi2Produced := by
  exact h.right.right.left

theorem dry_run_does_not_execute_official_planck
    (p : PlanckLikelihoodDryRunTarget)
    (_h : planckLikelihoodDryRunReady p)
    (hMissing : Not p.officialPlanckLikelihoodExecuted) :
    Not (planckLikelihoodPhysicalReady p) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4PlanckLikelihoodDryRunTarget
end JanusFormal
