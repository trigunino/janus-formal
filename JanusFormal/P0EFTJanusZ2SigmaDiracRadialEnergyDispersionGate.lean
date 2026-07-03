import JanusFormal.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate
import JanusFormal.P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGate

set_option autoImplicit false

structure DiracRadialEnergyDispersionGate where
  radialEnergyBibliographyChecked : Prop
  massTemperatureLawGateDeclared : Prop
  fermiDiracIsotropyGateDeclared : Prop
  comovingMomentumRedshiftDeclared : Prop
  plusEnergyFormulaDeclared : Prop
  minusEnergyFormulaDeclared : Prop
  scalarMassLawCriterionDeclared : Prop
  flrwMomentumFrameCriterionDeclared : Prop
  observationalFitForbidden : Prop
  plusMassLawReady : Prop
  minusMassLawReady : Prop
  plusScalarMassDerived : Prop
  minusScalarMassDerived : Prop
  plusFLRWMomentumFrameDerived : Prop
  minusFLRWMomentumFrameDerived : Prop
  plusRadialEnergyDerived : Prop
  minusRadialEnergyDerived : Prop
  projectedRadialEnergyDerived : Prop
  radialEnergyDispersionReady : Prop

def diracRadialEnergyDispersionLedgerDeclared
    (g : DiracRadialEnergyDispersionGate) : Prop :=
  g.radialEnergyBibliographyChecked /\
  g.massTemperatureLawGateDeclared /\
  g.fermiDiracIsotropyGateDeclared /\
  g.comovingMomentumRedshiftDeclared /\
  g.plusEnergyFormulaDeclared /\
  g.minusEnergyFormulaDeclared /\
  g.scalarMassLawCriterionDeclared /\
  g.flrwMomentumFrameCriterionDeclared /\
  g.observationalFitForbidden

def diracRadialEnergyDispersionReady
    (g : DiracRadialEnergyDispersionGate) : Prop :=
  diracRadialEnergyDispersionLedgerDeclared g /\
  g.plusMassLawReady /\
  g.minusMassLawReady /\
  g.plusScalarMassDerived /\
  g.minusScalarMassDerived /\
  g.plusFLRWMomentumFrameDerived /\
  g.minusFLRWMomentumFrameDerived /\
  g.plusRadialEnergyDerived /\
  g.minusRadialEnergyDerived /\
  g.projectedRadialEnergyDerived /\
  g.radialEnergyDispersionReady

theorem radial_energy_dispersion_requires_projected_radial_energy
    (g : DiracRadialEnergyDispersionGate)
    (hReady : diracRadialEnergyDispersionReady g) :
    g.projectedRadialEnergyDerived := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, _, hProjectedRadial, _⟩
  exact hProjectedRadial

end P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGate
end JanusFormal
