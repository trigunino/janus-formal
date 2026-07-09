import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaFermionRouteSelectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFermionDistributionOfAGate

set_option autoImplicit false

structure FermionDistributionOfAGate where
  fermionDistributionBibliographyChecked : Prop
  diracGasRouteDeclared : Prop
  weyssenhoffFluidRouteDeclared : Prop
  particleNumberConservationImported : Prop
  fermionRouteSelectionGateImported : Prop
  diracNumberDensityGateImported : Prop
  diracMassTemperatureLawGateImported : Prop
  diracThermalOccupationGateImported : Prop
  z2SigmaProjectionRequired : Prop
  thermodynamicSignPolicyDeclared : Prop
  observationalFitForbidden : Prop
  routeSelectedFromActionOrTopology : Prop
  fermionNumberDensityOfAReady : Prop
  fermionMassOrTemperatureLawReady : Prop
  plusFermionDistributionOfAReady : Prop
  minusFermionDistributionOfAReady : Prop
  projectedFermionDistributionOfAReady : Prop

def fermionDistributionLedgerDeclared
    (g : FermionDistributionOfAGate) : Prop :=
  g.fermionDistributionBibliographyChecked /\
  g.diracGasRouteDeclared /\
  g.weyssenhoffFluidRouteDeclared /\
  g.particleNumberConservationImported /\
  g.fermionRouteSelectionGateImported /\
  g.diracNumberDensityGateImported /\
  g.diracMassTemperatureLawGateImported /\
  g.diracThermalOccupationGateImported /\
  g.z2SigmaProjectionRequired /\
  g.thermodynamicSignPolicyDeclared /\
  g.observationalFitForbidden

def fermionDistributionOfAReady
    (g : FermionDistributionOfAGate) : Prop :=
  fermionDistributionLedgerDeclared g /\
  g.routeSelectedFromActionOrTopology /\
  g.fermionNumberDensityOfAReady /\
  g.fermionMassOrTemperatureLawReady /\
  g.plusFermionDistributionOfAReady /\
  g.minusFermionDistributionOfAReady /\
  g.projectedFermionDistributionOfAReady

theorem fermion_distribution_requires_route_selection
    (g : FermionDistributionOfAGate)
    (hReady : fermionDistributionOfAReady g) :
    g.routeSelectedFromActionOrTopology := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaFermionDistributionOfAGate
end JanusFormal
