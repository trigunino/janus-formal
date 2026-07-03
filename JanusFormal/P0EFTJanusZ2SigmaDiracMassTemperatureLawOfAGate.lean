import JanusFormal.P0EFTJanusZ2SigmaFermionRouteSelectionGate
import JanusFormal.P0EFTJanusZ2SigmaDiracRegimeSelectionGate
import JanusFormal.P0EFTJanusZ2SigmaDiracDecouplingConditionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate

set_option autoImplicit false

structure DiracMassTemperatureLawOfAGate where
  fermionThermalBibliographyChecked : Prop
  momentumRedshiftLawImported : Prop
  relativisticTemperatureScalingDeclared : Prop
  massiveDecoupledFermiGasGuardDeclared : Prop
  diracRegimeSelectionGateDeclared : Prop
  diracDecouplingConditionGateDeclared : Prop
  diracMassParameterDeclared : Prop
  z2SigmaProjectionRequired : Prop
  observationalFitForbidden : Prop
  relativisticOrMassiveRegimeDerived : Prop
  decouplingScaleDerived : Prop
  plusMassTemperatureLawReady : Prop
  minusMassTemperatureLawReady : Prop
  projectedMassTemperatureLawReady : Prop
  diracMassTemperatureLawOfAReady : Prop

def diracMassTemperatureLedgerDeclared
    (g : DiracMassTemperatureLawOfAGate) : Prop :=
  g.fermionThermalBibliographyChecked /\
  g.momentumRedshiftLawImported /\
  g.relativisticTemperatureScalingDeclared /\
  g.massiveDecoupledFermiGasGuardDeclared /\
  g.diracRegimeSelectionGateDeclared /\
  g.diracDecouplingConditionGateDeclared /\
  g.diracMassParameterDeclared /\
  g.z2SigmaProjectionRequired /\
  g.observationalFitForbidden

def diracMassTemperatureLawReady
    (g : DiracMassTemperatureLawOfAGate) : Prop :=
  diracMassTemperatureLedgerDeclared g /\
  g.relativisticOrMassiveRegimeDerived /\
  g.decouplingScaleDerived /\
  g.plusMassTemperatureLawReady /\
  g.minusMassTemperatureLawReady /\
  g.projectedMassTemperatureLawReady /\
  g.diracMassTemperatureLawOfAReady

theorem mass_temperature_law_requires_regime
    (g : DiracMassTemperatureLawOfAGate)
    (hReady : diracMassTemperatureLawReady g) :
    g.relativisticOrMassiveRegimeDerived := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate
end JanusFormal
