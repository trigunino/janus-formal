import JanusFormal.P0EFTJanusZ2SigmaFermionDistributionOfAGate
import JanusFormal.P0EFTJanusZ2SigmaDiracRegimeSelectionGate
import JanusFormal.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracEquationOfStateOfAGate

set_option autoImplicit false

structure DiracEquationOfStateOfAGate where
  kineticTheoryBibliographyChecked : Prop
  fermiDiracEnergyPressureIntegralsImported : Prop
  fermionDistributionGateDeclared : Prop
  diracRegimeSelectionGateDeclared : Prop
  diracMassTemperatureLawGateDeclared : Prop
  plusRhoIntegralDeclared : Prop
  plusPressureIntegralDeclared : Prop
  minusRhoIntegralDeclared : Prop
  minusPressureIntegralDeclared : Prop
  z2SigmaProjectionRequired : Prop
  observationalFitForbidden : Prop
  plusDistributionOfAReady : Prop
  minusDistributionOfAReady : Prop
  plusRegimeSelected : Prop
  minusRegimeSelected : Prop
  plusMassTemperatureLawReady : Prop
  minusMassTemperatureLawReady : Prop
  plusEquationOfStateDerived : Prop
  minusEquationOfStateDerived : Prop
  projectedEquationOfStateReady : Prop

def diracEquationOfStateLedgerDeclared
    (g : DiracEquationOfStateOfAGate) : Prop :=
  g.kineticTheoryBibliographyChecked /\
  g.fermiDiracEnergyPressureIntegralsImported /\
  g.fermionDistributionGateDeclared /\
  g.diracRegimeSelectionGateDeclared /\
  g.diracMassTemperatureLawGateDeclared /\
  g.plusRhoIntegralDeclared /\
  g.plusPressureIntegralDeclared /\
  g.minusRhoIntegralDeclared /\
  g.minusPressureIntegralDeclared /\
  g.z2SigmaProjectionRequired /\
  g.observationalFitForbidden

def diracEquationOfStateReady
    (g : DiracEquationOfStateOfAGate) : Prop :=
  diracEquationOfStateLedgerDeclared g /\
  g.plusDistributionOfAReady /\
  g.minusDistributionOfAReady /\
  g.plusRegimeSelected /\
  g.minusRegimeSelected /\
  g.plusMassTemperatureLawReady /\
  g.minusMassTemperatureLawReady /\
  g.plusEquationOfStateDerived /\
  g.minusEquationOfStateDerived /\
  g.projectedEquationOfStateReady

theorem dirac_eos_requires_distributions
    (g : DiracEquationOfStateOfAGate)
    (hReady : diracEquationOfStateReady g) :
    g.plusDistributionOfAReady /\ g.minusDistributionOfAReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaDiracEquationOfStateOfAGate
end JanusFormal
