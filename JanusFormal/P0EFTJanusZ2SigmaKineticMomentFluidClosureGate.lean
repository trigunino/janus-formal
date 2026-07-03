import JanusFormal.P0EFTJanusZ2SigmaDiracEquationOfStateOfAGate
import JanusFormal.P0EFTJanusZ2SigmaFermionDistributionOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaKineticMomentFluidClosureGate

set_option autoImplicit false

structure KineticMomentFluidClosureGate where
  kineticMomentBibliographyChecked : Prop
  stressEnergyMomentFormulaDeclared : Prop
  diracEquationOfStateGateDeclared : Prop
  fermionDistributionGateDeclared : Prop
  distributionIsotropyAnisotropicStressGateDeclared : Prop
  plusMomentStressDeclared : Prop
  minusMomentStressDeclared : Prop
  flrwIsotropyGuardDeclared : Prop
  anisotropicStressGuardDeclared : Prop
  z2SigmaProjectedFluidMomentDeclared : Prop
  observationalFitForbidden : Prop
  plusDistributionReady : Prop
  minusDistributionReady : Prop
  plusEquationOfStateReady : Prop
  minusEquationOfStateReady : Prop
  plusFLRWIsotropyDerived : Prop
  minusFLRWIsotropyDerived : Prop
  plusFluidMomentReady : Prop
  minusFluidMomentReady : Prop
  projectedFluidMomentReady : Prop

def kineticMomentFluidClosureLedgerDeclared
    (g : KineticMomentFluidClosureGate) : Prop :=
  g.kineticMomentBibliographyChecked /\
  g.stressEnergyMomentFormulaDeclared /\
  g.diracEquationOfStateGateDeclared /\
  g.fermionDistributionGateDeclared /\
  g.distributionIsotropyAnisotropicStressGateDeclared /\
  g.plusMomentStressDeclared /\
  g.minusMomentStressDeclared /\
  g.flrwIsotropyGuardDeclared /\
  g.anisotropicStressGuardDeclared /\
  g.z2SigmaProjectedFluidMomentDeclared /\
  g.observationalFitForbidden

def kineticMomentFluidClosureReady
    (g : KineticMomentFluidClosureGate) : Prop :=
  kineticMomentFluidClosureLedgerDeclared g /\
  g.plusDistributionReady /\
  g.minusDistributionReady /\
  g.plusEquationOfStateReady /\
  g.minusEquationOfStateReady /\
  g.plusFLRWIsotropyDerived /\
  g.minusFLRWIsotropyDerived /\
  g.plusFluidMomentReady /\
  g.minusFluidMomentReady /\
  g.projectedFluidMomentReady

theorem fluid_closure_requires_isotropy
    (g : KineticMomentFluidClosureGate)
    (hReady : kineticMomentFluidClosureReady g) :
    g.plusFLRWIsotropyDerived /\ g.minusFLRWIsotropyDerived := by
  rcases hReady with ⟨_, _, _, _, _, hPlusIso, hMinusIso, _, _, _⟩
  exact And.intro hPlusIso hMinusIso

end P0EFTJanusZ2SigmaKineticMomentFluidClosureGate
end JanusFormal
