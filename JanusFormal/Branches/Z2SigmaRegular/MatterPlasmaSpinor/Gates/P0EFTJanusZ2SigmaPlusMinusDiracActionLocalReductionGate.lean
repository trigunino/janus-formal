import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracMassTermFromActionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPlusMinusDiracActionLocalReductionGate

set_option autoImplicit false

structure PlusMinusDiracActionLocalReductionGate where
  curvedDiracLocalReductionBibliographyChecked : Prop
  plusMinusDiracMatterActionGateDeclared : Prop
  massTermFromActionGateDeclared : Prop
  kineticTermDeclared : Prop
  massBilinearTermDeclared : Prop
  axialTorsionCouplingDeclared : Prop
  localHermitianActionPolicyDeclared : Prop
  observationalFitForbidden : Prop
  plusMatterActionReady : Prop
  minusMatterActionReady : Prop
  plusKineticTermReduced : Prop
  minusKineticTermReduced : Prop
  plusMassBilinearReduced : Prop
  minusMassBilinearReduced : Prop
  plusAxialTorsionTermReduced : Prop
  minusAxialTorsionTermReduced : Prop
  plusMinusLocalReductionReady : Prop

def plusMinusDiracActionLocalReductionLedgerDeclared
    (g : PlusMinusDiracActionLocalReductionGate) : Prop :=
  g.curvedDiracLocalReductionBibliographyChecked /\
  g.plusMinusDiracMatterActionGateDeclared /\
  g.massTermFromActionGateDeclared /\
  g.kineticTermDeclared /\
  g.massBilinearTermDeclared /\
  g.axialTorsionCouplingDeclared /\
  g.localHermitianActionPolicyDeclared /\
  g.observationalFitForbidden

def plusMinusDiracActionLocalReductionReady
    (g : PlusMinusDiracActionLocalReductionGate) : Prop :=
  plusMinusDiracActionLocalReductionLedgerDeclared g /\
  g.plusMatterActionReady /\
  g.minusMatterActionReady /\
  g.plusKineticTermReduced /\
  g.minusKineticTermReduced /\
  g.plusMassBilinearReduced /\
  g.minusMassBilinearReduced /\
  g.plusAxialTorsionTermReduced /\
  g.minusAxialTorsionTermReduced /\
  g.plusMinusLocalReductionReady

theorem local_reduction_requires_mass_bilinears
    (g : PlusMinusDiracActionLocalReductionGate)
    (hReady : plusMinusDiracActionLocalReductionReady g) :
    g.plusMassBilinearReduced /\ g.minusMassBilinearReduced := by
  rcases hReady with ⟨_, _, _, _, _, hPlusMass, hMinusMass, _, _, _⟩
  exact And.intro hPlusMass hMinusMass

end P0EFTJanusZ2SigmaPlusMinusDiracActionLocalReductionGate
end JanusFormal
