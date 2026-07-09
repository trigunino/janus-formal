import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracNumberNormalizationGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracRegimeSelectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGate

set_option autoImplicit false

structure DiracChemicalPotentialOfAGate where
  fermiDiracChemicalPotentialBibliographyChecked : Prop
  numberConstraintEquationDeclared : Prop
  numberNormalizationGateDeclared : Prop
  massTemperatureLawGateDeclared : Prop
  regimeSelectionGateDeclared : Prop
  plusChemicalPotentialEquationDeclared : Prop
  minusChemicalPotentialEquationDeclared : Prop
  z2SigmaProjectedChemicalPotentialDeclared : Prop
  noChemicalPotentialFit : Prop
  observationalFitForbidden : Prop
  plusNumberNormalizationReady : Prop
  minusNumberNormalizationReady : Prop
  plusMassTemperatureLawReady : Prop
  minusMassTemperatureLawReady : Prop
  plusRegimeSelected : Prop
  minusRegimeSelected : Prop
  plusChemicalPotentialSolved : Prop
  minusChemicalPotentialSolved : Prop
  projectedChemicalPotentialReady : Prop

def diracChemicalPotentialLedgerDeclared
    (g : DiracChemicalPotentialOfAGate) : Prop :=
  g.fermiDiracChemicalPotentialBibliographyChecked /\
  g.numberConstraintEquationDeclared /\
  g.numberNormalizationGateDeclared /\
  g.massTemperatureLawGateDeclared /\
  g.regimeSelectionGateDeclared /\
  g.plusChemicalPotentialEquationDeclared /\
  g.minusChemicalPotentialEquationDeclared /\
  g.z2SigmaProjectedChemicalPotentialDeclared /\
  g.noChemicalPotentialFit /\
  g.observationalFitForbidden

def diracChemicalPotentialReady
    (g : DiracChemicalPotentialOfAGate) : Prop :=
  diracChemicalPotentialLedgerDeclared g /\
  g.plusNumberNormalizationReady /\
  g.minusNumberNormalizationReady /\
  g.plusMassTemperatureLawReady /\
  g.minusMassTemperatureLawReady /\
  g.plusRegimeSelected /\
  g.minusRegimeSelected /\
  g.plusChemicalPotentialSolved /\
  g.minusChemicalPotentialSolved /\
  g.projectedChemicalPotentialReady

theorem chemical_potential_requires_number_normalization
    (g : DiracChemicalPotentialOfAGate)
    (hReady : diracChemicalPotentialReady g) :
    g.plusNumberNormalizationReady /\ g.minusNumberNormalizationReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGate
end JanusFormal
