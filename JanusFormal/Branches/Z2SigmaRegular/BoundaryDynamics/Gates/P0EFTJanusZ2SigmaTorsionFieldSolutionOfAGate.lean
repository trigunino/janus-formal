import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaHolstTorsionStressOfAGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinCurrentOfAGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaImmirziProfileOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTorsionFieldSolutionOfAGate

set_option autoImplicit false

structure TorsionFieldSolutionOfAGate where
  torsionFieldBibliographyChecked : Prop
  sciamaKibbleCartanEquationImported : Prop
  holstConnectionVariationDeclared : Prop
  spinCurrentOfAGateDeclared : Prop
  algebraicTorsionConstraintDeclared : Prop
  spinCurrentSourceDeclared : Prop
  z2SigmaBoundaryTorsionSourceDeclared : Prop
  dynamicImmirziCouplingDeclared : Prop
  torsionIrreducibleDecompositionDeclared : Prop
  observationalFitForbidden : Prop
  spinCurrentOfAReady : Prop
  boundaryTorsionSourceOfAReady : Prop
  immirziProfileOfAReady : Prop
  torsionSolutionOfAReady : Prop

def torsionFieldLedgerDeclared
    (g : TorsionFieldSolutionOfAGate) : Prop :=
  g.torsionFieldBibliographyChecked /\
  g.sciamaKibbleCartanEquationImported /\
  g.holstConnectionVariationDeclared /\
  g.spinCurrentOfAGateDeclared /\
  g.algebraicTorsionConstraintDeclared /\
  g.spinCurrentSourceDeclared /\
  g.z2SigmaBoundaryTorsionSourceDeclared /\
  g.dynamicImmirziCouplingDeclared /\
  g.torsionIrreducibleDecompositionDeclared /\
  g.observationalFitForbidden

def torsionFieldSolutionReady
    (g : TorsionFieldSolutionOfAGate) : Prop :=
  torsionFieldLedgerDeclared g /\
  g.spinCurrentOfAReady /\
  g.boundaryTorsionSourceOfAReady /\
  g.immirziProfileOfAReady /\
  g.torsionSolutionOfAReady

theorem torsion_solution_requires_spin_current
    (g : TorsionFieldSolutionOfAGate)
    (hReady : torsionFieldSolutionReady g) :
    g.spinCurrentOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaTorsionFieldSolutionOfAGate
end JanusFormal
