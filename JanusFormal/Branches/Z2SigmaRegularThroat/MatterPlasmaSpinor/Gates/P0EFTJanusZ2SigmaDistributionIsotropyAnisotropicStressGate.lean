import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaFermionDistributionOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGate

set_option autoImplicit false

structure DistributionIsotropyAnisotropicStressGate where
  isotropicDistributionBibliographyChecked : Prop
  fermionDistributionGateDeclared : Prop
  plusMomentumIsotropyCriterionDeclared : Prop
  minusMomentumIsotropyCriterionDeclared : Prop
  projectedIsotropyCriterionDeclared : Prop
  anisotropicStressTensorDeclared : Prop
  noAnisotropicStressAssumption : Prop
  observationalFitForbidden : Prop
  plusDistributionReady : Prop
  minusDistributionReady : Prop
  plusMomentumIsotropyDerived : Prop
  minusMomentumIsotropyDerived : Prop
  projectedMomentumIsotropyDerived : Prop
  plusAnisotropicStressZeroDerived : Prop
  minusAnisotropicStressZeroDerived : Prop
  projectedAnisotropicStressZeroDerived : Prop
  flrwIsotropyClosureReady : Prop

def distributionIsotropyLedgerDeclared
    (g : DistributionIsotropyAnisotropicStressGate) : Prop :=
  g.isotropicDistributionBibliographyChecked /\
  g.fermionDistributionGateDeclared /\
  g.plusMomentumIsotropyCriterionDeclared /\
  g.minusMomentumIsotropyCriterionDeclared /\
  g.projectedIsotropyCriterionDeclared /\
  g.anisotropicStressTensorDeclared /\
  g.noAnisotropicStressAssumption /\
  g.observationalFitForbidden

def distributionIsotropyClosureReady
    (g : DistributionIsotropyAnisotropicStressGate) : Prop :=
  distributionIsotropyLedgerDeclared g /\
  g.plusDistributionReady /\
  g.minusDistributionReady /\
  g.plusMomentumIsotropyDerived /\
  g.minusMomentumIsotropyDerived /\
  g.projectedMomentumIsotropyDerived /\
  g.plusAnisotropicStressZeroDerived /\
  g.minusAnisotropicStressZeroDerived /\
  g.projectedAnisotropicStressZeroDerived /\
  g.flrwIsotropyClosureReady

theorem isotropy_closure_requires_projected_isotropy
    (g : DistributionIsotropyAnisotropicStressGate)
    (hReady : distributionIsotropyClosureReady g) :
    g.projectedMomentumIsotropyDerived := by
  rcases hReady with ⟨_, _, _, _, _, hProjectedIso, _, _, _, _⟩
  exact hProjectedIso

theorem isotropy_closure_requires_projected_anisotropic_stress_zero
    (g : DistributionIsotropyAnisotropicStressGate)
    (hReady : distributionIsotropyClosureReady g) :
    g.projectedAnisotropicStressZeroDerived := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, hProjectedPiZero, _⟩
  exact hProjectedPiZero

end P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGate
end JanusFormal
