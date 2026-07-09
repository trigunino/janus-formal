import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracScalarMassLawGate

set_option autoImplicit false

structure DiracScalarMassLawGate where
  diracMassScalarBibliographyChecked : Prop
  projectedDiracActionGateDeclared : Prop
  massTemperatureLawGateDeclared : Prop
  plusMassTermDeclared : Prop
  minusMassTermDeclared : Prop
  scalarUnderLocalLorentzCriterionDeclared : Prop
  z2SigmaProjectionMassCriterionDeclared : Prop
  observationalFitForbidden : Prop
  plusProjectedDiracActionReady : Prop
  minusProjectedDiracActionReady : Prop
  plusMassTermFromActionDerived : Prop
  minusMassTermFromActionDerived : Prop
  plusScalarMassDerived : Prop
  minusScalarMassDerived : Prop
  projectedScalarMassDerived : Prop
  scalarMassLawReady : Prop

def diracScalarMassLawLedgerDeclared
    (g : DiracScalarMassLawGate) : Prop :=
  g.diracMassScalarBibliographyChecked /\
  g.projectedDiracActionGateDeclared /\
  g.massTemperatureLawGateDeclared /\
  g.plusMassTermDeclared /\
  g.minusMassTermDeclared /\
  g.scalarUnderLocalLorentzCriterionDeclared /\
  g.z2SigmaProjectionMassCriterionDeclared /\
  g.observationalFitForbidden

def diracScalarMassLawReady
    (g : DiracScalarMassLawGate) : Prop :=
  diracScalarMassLawLedgerDeclared g /\
  g.plusProjectedDiracActionReady /\
  g.minusProjectedDiracActionReady /\
  g.plusMassTermFromActionDerived /\
  g.minusMassTermFromActionDerived /\
  g.plusScalarMassDerived /\
  g.minusScalarMassDerived /\
  g.projectedScalarMassDerived /\
  g.scalarMassLawReady

theorem scalar_mass_law_requires_action_mass_terms
    (g : DiracScalarMassLawGate)
    (hReady : diracScalarMassLawReady g) :
    g.plusMassTermFromActionDerived /\ g.minusMassTermFromActionDerived := by
  rcases hReady with ⟨_, _, _, hPlusMass, hMinusMass, _, _, _, _⟩
  exact And.intro hPlusMass hMinusMass

end P0EFTJanusZ2SigmaDiracScalarMassLawGate
end JanusFormal
