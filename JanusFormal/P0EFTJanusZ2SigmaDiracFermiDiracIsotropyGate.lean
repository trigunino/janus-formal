import JanusFormal.P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate
import JanusFormal.P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate

set_option autoImplicit false

structure DiracFermiDiracIsotropyGate where
  fermiDiracIsotropyBibliographyChecked : Prop
  thermalOccupationGateDeclared : Prop
  distributionIsotropyGateDeclared : Prop
  radialEnergyCriterionDeclared : Prop
  plusRadialOccupationCriterionDeclared : Prop
  minusRadialOccupationCriterionDeclared : Prop
  projectionPreservesIsotropyCriterionDeclared : Prop
  observationalFitForbidden : Prop
  plusThermalOccupationReady : Prop
  minusThermalOccupationReady : Prop
  plusEnergyRadialDerived : Prop
  minusEnergyRadialDerived : Prop
  projectedOccupationRadialDerived : Prop
  plusMomentumIsotropyDerived : Prop
  minusMomentumIsotropyDerived : Prop
  projectedMomentumIsotropyDerived : Prop
  fermiDiracIsotropyClosureReady : Prop

def diracFermiDiracIsotropyLedgerDeclared
    (g : DiracFermiDiracIsotropyGate) : Prop :=
  g.fermiDiracIsotropyBibliographyChecked /\
  g.thermalOccupationGateDeclared /\
  g.distributionIsotropyGateDeclared /\
  g.radialEnergyCriterionDeclared /\
  g.plusRadialOccupationCriterionDeclared /\
  g.minusRadialOccupationCriterionDeclared /\
  g.projectionPreservesIsotropyCriterionDeclared /\
  g.observationalFitForbidden

def diracFermiDiracIsotropyReady
    (g : DiracFermiDiracIsotropyGate) : Prop :=
  diracFermiDiracIsotropyLedgerDeclared g /\
  g.plusThermalOccupationReady /\
  g.minusThermalOccupationReady /\
  g.plusEnergyRadialDerived /\
  g.minusEnergyRadialDerived /\
  g.projectedOccupationRadialDerived /\
  g.plusMomentumIsotropyDerived /\
  g.minusMomentumIsotropyDerived /\
  g.projectedMomentumIsotropyDerived /\
  g.fermiDiracIsotropyClosureReady

theorem fermi_dirac_isotropy_requires_projected_radial_occupation
    (g : DiracFermiDiracIsotropyGate)
    (hReady : diracFermiDiracIsotropyReady g) :
    g.projectedOccupationRadialDerived := by
  rcases hReady with ⟨_, _, _, _, _, hProjectedRadial, _, _, _, _⟩
  exact hProjectedRadial

theorem fermi_dirac_isotropy_supplies_projected_momentum_isotropy
    (g : DiracFermiDiracIsotropyGate)
    (hReady : diracFermiDiracIsotropyReady g) :
    g.projectedMomentumIsotropyDerived := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, hProjectedIso, _⟩
  exact hProjectedIso

end P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate
end JanusFormal
