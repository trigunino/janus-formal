import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracInteractionRateOfAGate

set_option autoImplicit false

structure DiracInteractionRateOfAGate where
  interactionRateBibliographyChecked : Prop
  gammaEqualsNumberDensityTimesThermalCrossSectionImported : Prop
  plusBathDensityDeclared : Prop
  minusBathDensityDeclared : Prop
  plusThermalCrossSectionDeclared : Prop
  minusThermalCrossSectionDeclared : Prop
  thermalCrossSectionGateDeclared : Prop
  z2SigmaProjectionRequired : Prop
  observationalFitForbidden : Prop
  plusBathDensityOfAReady : Prop
  minusBathDensityOfAReady : Prop
  plusThermalCrossSectionOfAReady : Prop
  minusThermalCrossSectionOfAReady : Prop
  plusInteractionRateOfAReady : Prop
  minusInteractionRateOfAReady : Prop
  projectedInteractionRateOfAReady : Prop
  diracInteractionRateOfAReady : Prop

def diracInteractionRateLedgerDeclared
    (g : DiracInteractionRateOfAGate) : Prop :=
  g.interactionRateBibliographyChecked /\
  g.gammaEqualsNumberDensityTimesThermalCrossSectionImported /\
  g.plusBathDensityDeclared /\
  g.minusBathDensityDeclared /\
  g.plusThermalCrossSectionDeclared /\
  g.minusThermalCrossSectionDeclared /\
  g.thermalCrossSectionGateDeclared /\
  g.z2SigmaProjectionRequired /\
  g.observationalFitForbidden

def diracInteractionRateReady
    (g : DiracInteractionRateOfAGate) : Prop :=
  diracInteractionRateLedgerDeclared g /\
  g.plusBathDensityOfAReady /\
  g.minusBathDensityOfAReady /\
  g.plusThermalCrossSectionOfAReady /\
  g.minusThermalCrossSectionOfAReady /\
  g.plusInteractionRateOfAReady /\
  g.minusInteractionRateOfAReady /\
  g.projectedInteractionRateOfAReady /\
  g.diracInteractionRateOfAReady

theorem interaction_rate_requires_bath_and_cross_section
    (g : DiracInteractionRateOfAGate)
    (hReady : diracInteractionRateReady g) :
    g.plusBathDensityOfAReady /\ g.plusThermalCrossSectionOfAReady /\
      g.minusBathDensityOfAReady /\ g.minusThermalCrossSectionOfAReady := by
  exact And.intro hReady.2.1
    (And.intro hReady.2.2.2.1
      (And.intro hReady.2.2.1 hReady.2.2.2.2.1))

end P0EFTJanusZ2SigmaDiracInteractionRateOfAGate
end JanusFormal
