import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracNumberNormalizationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracRegimeSelectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracDegeneracyFactorGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate

set_option autoImplicit false

structure DiracThermalOccupationOfAGate where
  fermiDiracBibliographyChecked : Prop
  fermiDiracOccupationDeclared : Prop
  chemicalPotentialPolicyDeclared : Prop
  chemicalPotentialGateDeclared : Prop
  degeneracyFactorDeclared : Prop
  degeneracyFactorGateDeclared : Prop
  numberNormalizationGateDeclared : Prop
  massTemperatureLawGateDeclared : Prop
  regimeSelectionGateDeclared : Prop
  plusOccupationDeclared : Prop
  minusOccupationDeclared : Prop
  z2SigmaProjectedOccupationDeclared : Prop
  observationalFitForbidden : Prop
  plusNumberNormalizationReady : Prop
  minusNumberNormalizationReady : Prop
  plusMassTemperatureLawReady : Prop
  minusMassTemperatureLawReady : Prop
  plusRegimeSelected : Prop
  minusRegimeSelected : Prop
  plusChemicalPotentialDerived : Prop
  minusChemicalPotentialDerived : Prop
  plusThermalOccupationReady : Prop
  minusThermalOccupationReady : Prop
  projectedThermalOccupationReady : Prop

def diracThermalOccupationLedgerDeclared
    (g : DiracThermalOccupationOfAGate) : Prop :=
  g.fermiDiracBibliographyChecked /\
  g.fermiDiracOccupationDeclared /\
  g.chemicalPotentialPolicyDeclared /\
  g.chemicalPotentialGateDeclared /\
  g.degeneracyFactorDeclared /\
  g.degeneracyFactorGateDeclared /\
  g.numberNormalizationGateDeclared /\
  g.massTemperatureLawGateDeclared /\
  g.regimeSelectionGateDeclared /\
  g.plusOccupationDeclared /\
  g.minusOccupationDeclared /\
  g.z2SigmaProjectedOccupationDeclared /\
  g.observationalFitForbidden

def diracThermalOccupationReady
    (g : DiracThermalOccupationOfAGate) : Prop :=
  diracThermalOccupationLedgerDeclared g /\
  g.plusNumberNormalizationReady /\
  g.minusNumberNormalizationReady /\
  g.plusMassTemperatureLawReady /\
  g.minusMassTemperatureLawReady /\
  g.plusRegimeSelected /\
  g.minusRegimeSelected /\
  g.plusChemicalPotentialDerived /\
  g.minusChemicalPotentialDerived /\
  g.plusThermalOccupationReady /\
  g.minusThermalOccupationReady /\
  g.projectedThermalOccupationReady

theorem thermal_occupation_requires_number_normalization
    (g : DiracThermalOccupationOfAGate)
    (hReady : diracThermalOccupationReady g) :
    g.plusNumberNormalizationReady /\ g.minusNumberNormalizationReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate
end JanusFormal
