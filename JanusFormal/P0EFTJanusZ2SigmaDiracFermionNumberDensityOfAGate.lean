import JanusFormal.P0EFTJanusZ2SigmaFermionRouteSelectionGate
import JanusFormal.P0EFTJanusZ2SigmaDiracNumberNormalizationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate

set_option autoImplicit false

structure DiracFermionNumberDensityOfAGate where
  diracNumberDensityBibliographyChecked : Prop
  diracU1CurrentImported : Prop
  covariantCurrentConservationDeclared : Prop
  flrwDilutionLawDerived : Prop
  diracNumberNormalizationGateDeclared : Prop
  anomalyOrSourceGuardDeclared : Prop
  z2SigmaProjectionRequired : Prop
  observationalFitForbidden : Prop
  plusNumberNormalizationDerived : Prop
  minusNumberNormalizationDerived : Prop
  projectedNumberDensityReady : Prop
  diracFermionNumberDensityOfAReady : Prop

def diracNumberDensityLedgerDeclared
    (g : DiracFermionNumberDensityOfAGate) : Prop :=
  g.diracNumberDensityBibliographyChecked /\
  g.diracU1CurrentImported /\
  g.covariantCurrentConservationDeclared /\
  g.flrwDilutionLawDerived /\
  g.diracNumberNormalizationGateDeclared /\
  g.anomalyOrSourceGuardDeclared /\
  g.z2SigmaProjectionRequired /\
  g.observationalFitForbidden

def diracFermionNumberDensityReady
    (g : DiracFermionNumberDensityOfAGate) : Prop :=
  diracNumberDensityLedgerDeclared g /\
  g.plusNumberNormalizationDerived /\
  g.minusNumberNormalizationDerived /\
  g.projectedNumberDensityReady /\
  g.diracFermionNumberDensityOfAReady

theorem dirac_number_density_requires_normalizations
    (g : DiracFermionNumberDensityOfAGate)
    (hReady : diracFermionNumberDensityReady g) :
    g.plusNumberNormalizationDerived /\ g.minusNumberNormalizationDerived := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate
end JanusFormal
