namespace JanusFormal
namespace P0EFTJanusZ4PlanckAdapterContract

set_option autoImplicit false

structure PlanckAdapterContract where
  ttSpectrumExportDeclared : Prop
  teSpectrumExportDeclared : Prop
  eeSpectrumExportDeclared : Prop
  lensingSpectrumExportDeclared : Prop
  ellGridAndUnitsDeclared : Prop
  covarianceOrLikelihoodDeclared : Prop
  directPlanckLikelihoodExecuted : Prop

def adapterContractReady (p : PlanckAdapterContract) : Prop :=
  p.ttSpectrumExportDeclared /\
  p.teSpectrumExportDeclared /\
  p.eeSpectrumExportDeclared /\
  p.lensingSpectrumExportDeclared /\
  p.ellGridAndUnitsDeclared /\
  p.covarianceOrLikelihoodDeclared

def adapterPhysicalReady (p : PlanckAdapterContract) : Prop :=
  adapterContractReady p /\
  p.directPlanckLikelihoodExecuted

theorem adapter_contract_does_not_execute_planck
    (p : PlanckAdapterContract)
    (_ready : adapterContractReady p)
    (hMissing : Not p.directPlanckLikelihoodExecuted) :
    Not (adapterPhysicalReady p) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4PlanckAdapterContract
end JanusFormal
