import JanusFormal.P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate
import JanusFormal.P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate

set_option autoImplicit false

structure PlusMinusMatterCurrentGate where
  diracNoetherCurrentBibliographyChecked : Prop
  plusMinusDiracMatterActionGateDeclared : Prop
  plusMinusMatterActionsDeclared : Prop
  diracCurrentFormulaImported : Prop
  plusCurrentDeclared : Prop
  minusCurrentDeclared : Prop
  covariantConservationGuardDeclared : Prop
  observationalFitForbidden : Prop
  plusMatterActionReady : Prop
  minusMatterActionReady : Prop
  plusCurrentReady : Prop
  minusCurrentReady : Prop
  plusMinusMatterCurrentsReady : Prop

def plusMinusMatterCurrentLedgerDeclared
    (g : PlusMinusMatterCurrentGate) : Prop :=
  g.diracNoetherCurrentBibliographyChecked /\
  g.plusMinusDiracMatterActionGateDeclared /\
  g.plusMinusMatterActionsDeclared /\
  g.diracCurrentFormulaImported /\
  g.plusCurrentDeclared /\
  g.minusCurrentDeclared /\
  g.covariantConservationGuardDeclared /\
  g.observationalFitForbidden

def plusMinusMatterCurrentReady
    (g : PlusMinusMatterCurrentGate) : Prop :=
  plusMinusMatterCurrentLedgerDeclared g /\
  g.plusMatterActionReady /\
  g.minusMatterActionReady /\
  g.plusCurrentReady /\
  g.minusCurrentReady /\
  g.plusMinusMatterCurrentsReady

theorem plus_minus_currents_require_matter_actions
    (g : PlusMinusMatterCurrentGate)
    (hReady : plusMinusMatterCurrentReady g) :
    g.plusMatterActionReady /\ g.minusMatterActionReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate
end JanusFormal
