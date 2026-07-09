import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaFermionDistributionOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinCurrentOfAGate

set_option autoImplicit false

structure SpinCurrentOfAGate where
  spinCurrentBibliographyChecked : Prop
  canonicalSpinTensorFormulaImported : Prop
  diracAxialCurrentRelationDeclared : Prop
  plusSectorSpinCurrentDeclared : Prop
  minusSectorSpinCurrentDeclared : Prop
  fermionDistributionOfAGateDeclared : Prop
  spinAveragingPolicyDeclared : Prop
  z2SignPolicyDeclared : Prop
  observationalFitForbidden : Prop
  fermionDistributionOfAReady : Prop
  spinPolarizationOfAReady : Prop
  plusSpinCurrentOfAReady : Prop
  minusSpinCurrentOfAReady : Prop
  projectedSpinCurrentOfAReady : Prop

def spinCurrentLedgerDeclared
    (g : SpinCurrentOfAGate) : Prop :=
  g.spinCurrentBibliographyChecked /\
  g.canonicalSpinTensorFormulaImported /\
  g.diracAxialCurrentRelationDeclared /\
  g.plusSectorSpinCurrentDeclared /\
  g.minusSectorSpinCurrentDeclared /\
  g.fermionDistributionOfAGateDeclared /\
  g.spinAveragingPolicyDeclared /\
  g.z2SignPolicyDeclared /\
  g.observationalFitForbidden

def spinCurrentOfAReady
    (g : SpinCurrentOfAGate) : Prop :=
  spinCurrentLedgerDeclared g /\
  g.fermionDistributionOfAReady /\
  g.spinPolarizationOfAReady /\
  g.plusSpinCurrentOfAReady /\
  g.minusSpinCurrentOfAReady /\
  g.projectedSpinCurrentOfAReady

theorem spin_current_requires_fermion_distribution
    (g : SpinCurrentOfAGate)
    (hReady : spinCurrentOfAReady g) :
    g.fermionDistributionOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaSpinCurrentOfAGate
end JanusFormal
