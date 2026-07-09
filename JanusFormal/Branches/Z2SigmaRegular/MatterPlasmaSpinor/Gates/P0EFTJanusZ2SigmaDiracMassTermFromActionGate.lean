import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracScalarMassLawGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracMassTermFromActionGate

set_option autoImplicit false

structure DiracMassTermFromActionGate where
  diracMassTermBibliographyChecked : Prop
  projectedDiracActionGateDeclared : Prop
  scalarMassLawGateDeclared : Prop
  massBilinearDeclared : Prop
  plusMassCoefficientDeclared : Prop
  minusMassCoefficientDeclared : Prop
  z2SigmaProjectedMassCoefficientDeclared : Prop
  observationalFitForbidden : Prop
  projectedDiracActionReady : Prop
  plusDiracActionReduced : Prop
  minusDiracActionReduced : Prop
  plusMassBilinearIdentified : Prop
  minusMassBilinearIdentified : Prop
  plusMassCoefficientFromActionDerived : Prop
  minusMassCoefficientFromActionDerived : Prop
  projectedMassCoefficientDerived : Prop
  massTermFromActionReady : Prop

def diracMassTermFromActionLedgerDeclared
    (g : DiracMassTermFromActionGate) : Prop :=
  g.diracMassTermBibliographyChecked /\
  g.projectedDiracActionGateDeclared /\
  g.scalarMassLawGateDeclared /\
  g.massBilinearDeclared /\
  g.plusMassCoefficientDeclared /\
  g.minusMassCoefficientDeclared /\
  g.z2SigmaProjectedMassCoefficientDeclared /\
  g.observationalFitForbidden

def diracMassTermFromActionReady
    (g : DiracMassTermFromActionGate) : Prop :=
  diracMassTermFromActionLedgerDeclared g /\
  g.projectedDiracActionReady /\
  g.plusDiracActionReduced /\
  g.minusDiracActionReduced /\
  g.plusMassBilinearIdentified /\
  g.minusMassBilinearIdentified /\
  g.plusMassCoefficientFromActionDerived /\
  g.minusMassCoefficientFromActionDerived /\
  g.projectedMassCoefficientDerived /\
  g.massTermFromActionReady

theorem mass_term_from_action_requires_projected_coefficient
    (g : DiracMassTermFromActionGate)
    (hReady : diracMassTermFromActionReady g) :
    g.projectedMassCoefficientDerived := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, hProjectedCoeff, _⟩
  exact hProjectedCoeff

end P0EFTJanusZ2SigmaDiracMassTermFromActionGate
end JanusFormal
