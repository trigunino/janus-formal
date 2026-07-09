import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaBackgroundEquationDerivationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracInteractionRateOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaNumericalBackgroundClosureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracDecouplingConditionGate

set_option autoImplicit false

structure DiracDecouplingConditionGate where
  decouplingBibliographyChecked : Prop
  gammaEqualsHCriterionImported : Prop
  plusInteractionRateDeclared : Prop
  minusInteractionRateDeclared : Prop
  interactionRateGateDeclared : Prop
  z2SigmaHubbleRateRequired : Prop
  numericalBackgroundClosureGateDeclared : Prop
  boundaryConditionRouteDeclared : Prop
  observationalFitForbidden : Prop
  plusInteractionRateOfAReady : Prop
  minusInteractionRateOfAReady : Prop
  hZ2SigmaOfAReady : Prop
  plusDecouplingScaleReady : Prop
  minusDecouplingScaleReady : Prop
  projectedDecouplingScaleReady : Prop
  diracDecouplingConditionReady : Prop

def diracDecouplingLedgerDeclared
    (g : DiracDecouplingConditionGate) : Prop :=
  g.decouplingBibliographyChecked /\
  g.gammaEqualsHCriterionImported /\
  g.plusInteractionRateDeclared /\
  g.minusInteractionRateDeclared /\
  g.interactionRateGateDeclared /\
  g.z2SigmaHubbleRateRequired /\
  g.numericalBackgroundClosureGateDeclared /\
  g.boundaryConditionRouteDeclared /\
  g.observationalFitForbidden

def diracDecouplingReady
    (g : DiracDecouplingConditionGate) : Prop :=
  diracDecouplingLedgerDeclared g /\
  g.plusInteractionRateOfAReady /\
  g.minusInteractionRateOfAReady /\
  g.hZ2SigmaOfAReady /\
  g.plusDecouplingScaleReady /\
  g.minusDecouplingScaleReady /\
  g.projectedDecouplingScaleReady /\
  g.diracDecouplingConditionReady

theorem decoupling_requires_rates_and_background
    (g : DiracDecouplingConditionGate)
    (hReady : diracDecouplingReady g) :
    g.plusInteractionRateOfAReady /\ g.minusInteractionRateOfAReady /\ g.hZ2SigmaOfAReady := by
  exact And.intro hReady.2.1 (And.intro hReady.2.2.1 hReady.2.2.2.1)

end P0EFTJanusZ2SigmaDiracDecouplingConditionGate
end JanusFormal
