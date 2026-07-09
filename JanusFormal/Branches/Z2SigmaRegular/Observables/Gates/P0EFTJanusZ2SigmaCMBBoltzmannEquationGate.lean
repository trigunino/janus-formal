import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate
import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaGrowthPerturbationEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCMBBoltzmannEquationGate

set_option autoImplicit false

structure Z2SigmaCMBBoltzmannEquationGate where
  cmbBibliographyChecked : Prop
  growthPerturbationEquationsDerived : Prop
  photonTemperatureHierarchyDeclared : Prop
  photonPolarizationHierarchyDeclared : Prop
  baryonEulerContinuityCouplingDeclared : Prop
  neutrinoHierarchyDeclared : Prop
  z2SigmaMetricSourceTermsDerived : Prop
  visibilityAndRecombinationPolicyDeclared : Prop
  archivedZ4CMBReuseForbidden : Prop
  cmbBoltzmannEquationsDerived : Prop

def cmbBoltzmannLockClosed
    (g : Z2SigmaCMBBoltzmannEquationGate) : Prop :=
  g.cmbBibliographyChecked /\
  g.growthPerturbationEquationsDerived /\
  g.photonTemperatureHierarchyDeclared /\
  g.photonPolarizationHierarchyDeclared /\
  g.baryonEulerContinuityCouplingDeclared /\
  g.neutrinoHierarchyDeclared /\
  g.z2SigmaMetricSourceTermsDerived /\
  g.visibilityAndRecombinationPolicyDeclared /\
  g.archivedZ4CMBReuseForbidden

theorem cmb_boltzmann_lock_derives_equations
    (g : Z2SigmaCMBBoltzmannEquationGate)
    (hLock : cmbBoltzmannLockClosed g)
    (hImplies : cmbBoltzmannLockClosed g -> g.cmbBoltzmannEquationsDerived) :
    g.cmbBoltzmannEquationsDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaCMBBoltzmannEquationGate
end JanusFormal
