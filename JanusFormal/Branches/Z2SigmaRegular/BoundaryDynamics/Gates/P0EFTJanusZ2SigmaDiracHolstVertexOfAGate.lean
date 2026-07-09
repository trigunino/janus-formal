import JanusFormal.Basic
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaImmirziProfileOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracHolstVertexOfAGate

set_option autoImplicit false

structure DiracHolstVertexOfAGate where
  vertexBibliographyChecked : Prop
  holstFermionFourFermionVertexImported : Prop
  axialAxialChannelDeclared : Prop
  immirziDependentCouplingDeclared : Prop
  torsionFieldSolutionRequired : Prop
  spinCurrentRequired : Prop
  z2SigmaBoundaryProjectionRequired : Prop
  observationalFitForbidden : Prop
  torsionFieldSolutionOfAReady : Prop
  spinCurrentOfAReady : Prop
  immirziProfileOfAReady : Prop
  plusVertexReady : Prop
  minusVertexReady : Prop
  projectedVertexReady : Prop
  plusMatrixElementReady : Prop
  minusMatrixElementReady : Prop
  diracHolstVertexOfAReady : Prop

def diracHolstVertexLedgerDeclared
    (g : DiracHolstVertexOfAGate) : Prop :=
  g.vertexBibliographyChecked /\
  g.holstFermionFourFermionVertexImported /\
  g.axialAxialChannelDeclared /\
  g.immirziDependentCouplingDeclared /\
  g.torsionFieldSolutionRequired /\
  g.spinCurrentRequired /\
  g.z2SigmaBoundaryProjectionRequired /\
  g.observationalFitForbidden

def diracHolstVertexReady
    (g : DiracHolstVertexOfAGate) : Prop :=
  diracHolstVertexLedgerDeclared g /\
  g.torsionFieldSolutionOfAReady /\
  g.spinCurrentOfAReady /\
  g.immirziProfileOfAReady /\
  g.plusVertexReady /\
  g.minusVertexReady /\
  g.projectedVertexReady /\
  g.plusMatrixElementReady /\
  g.minusMatrixElementReady /\
  g.diracHolstVertexOfAReady

theorem matrix_elements_require_projected_vertex
    (g : DiracHolstVertexOfAGate)
    (hReady : diracHolstVertexReady g) :
    g.projectedVertexReady /\ g.plusMatrixElementReady /\ g.minusMatrixElementReady := by
  exact And.intro hReady.2.2.2.2.2.2.1
    (And.intro hReady.2.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.2.2.1)

end P0EFTJanusZ2SigmaDiracHolstVertexOfAGate
end JanusFormal
