import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaFermionRouteSelectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracDecouplingConditionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracRegimeSelectionGate

set_option autoImplicit false

structure DiracRegimeSelectionGate where
  regimeBibliographyChecked : Prop
  massOverDecouplingTemperatureCriterionDeclared : Prop
  diracDecouplingConditionGateDeclared : Prop
  relativisticRouteDeclared : Prop
  massiveRouteDeclared : Prop
  semiRelativisticRouteDeclared : Prop
  noRegimeChosenByFit : Prop
  observationalFitForbidden : Prop
  plusMassOverTdecDerived : Prop
  minusMassOverTdecDerived : Prop
  plusRegimeSelected : Prop
  minusRegimeSelected : Prop
  projectedRegimeSelected : Prop
  diracRegimeSelectionReady : Prop

def diracRegimeLedgerDeclared
    (g : DiracRegimeSelectionGate) : Prop :=
  g.regimeBibliographyChecked /\
  g.massOverDecouplingTemperatureCriterionDeclared /\
  g.diracDecouplingConditionGateDeclared /\
  g.relativisticRouteDeclared /\
  g.massiveRouteDeclared /\
  g.semiRelativisticRouteDeclared /\
  g.noRegimeChosenByFit /\
  g.observationalFitForbidden

def diracRegimeReady
    (g : DiracRegimeSelectionGate) : Prop :=
  diracRegimeLedgerDeclared g /\
  g.plusMassOverTdecDerived /\
  g.minusMassOverTdecDerived /\
  g.plusRegimeSelected /\
  g.minusRegimeSelected /\
  g.projectedRegimeSelected /\
  g.diracRegimeSelectionReady

theorem dirac_regime_requires_mass_over_tdec
    (g : DiracRegimeSelectionGate)
    (hReady : diracRegimeReady g) :
    g.plusMassOverTdecDerived /\ g.minusMassOverTdecDerived := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaDiracRegimeSelectionGate
end JanusFormal
