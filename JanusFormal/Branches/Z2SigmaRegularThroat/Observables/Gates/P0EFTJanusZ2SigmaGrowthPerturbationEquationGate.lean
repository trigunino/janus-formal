import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate
import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaGrowthBibliographyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaGrowthPerturbationEquationGate

set_option autoImplicit false

structure Z2SigmaGrowthPerturbationEquationGate where
  backgroundEquationsDerived : Prop
  growthBibliographyChecked : Prop
  scalarPerturbationGaugeDeclared : Prop
  densityContinuityPerturbationDerived : Prop
  velocityEulerPerturbationDerived : Prop
  z2SigmaPoissonConstraintDerived : Prop
  z2SigmaSlipRelationDerived : Prop
  z2SigmaFrictionTermDerived : Prop
  archivedZ4MuReuseForbidden : Prop
  growthPerturbationEquationsDerived : Prop

def growthPerturbationLockClosed
    (g : Z2SigmaGrowthPerturbationEquationGate) : Prop :=
  g.backgroundEquationsDerived /\
  g.growthBibliographyChecked /\
  g.scalarPerturbationGaugeDeclared /\
  g.densityContinuityPerturbationDerived /\
  g.velocityEulerPerturbationDerived /\
  g.z2SigmaPoissonConstraintDerived /\
  g.z2SigmaSlipRelationDerived /\
  g.z2SigmaFrictionTermDerived /\
  g.archivedZ4MuReuseForbidden

theorem growth_lock_derives_perturbation_equations
    (g : Z2SigmaGrowthPerturbationEquationGate)
    (hLock : growthPerturbationLockClosed g)
    (hImplies : growthPerturbationLockClosed g -> g.growthPerturbationEquationsDerived) :
    g.growthPerturbationEquationsDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaGrowthPerturbationEquationGate
end JanusFormal
