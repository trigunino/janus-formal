import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate

set_option autoImplicit false

structure CountertermLocalDensityBasisGate where
  nonlinearResidualClosureImported : Prop
  boundaryCountertermBibliographyChecked : Prop
  activeVariableBasisDeclared : Prop
  hBlockDeclared : Prop
  kBlockDeclared : Prop
  torsionPullbackBlockDeclared : Prop
  immirziBoundaryBlockDeclared : Prop
  z2OrientationBlockDeclared : Prop
  noNewCountertermFreedomDeclared : Prop
  observationalFitForbidden : Prop
  uniqueCountertermTransported : Prop
  localDensityBasisComplete : Prop
  lCtLocalExpansionDerived : Prop
  lCtReadyForDensityExpansionGate : Prop

def countertermLocalDensityBasisLedgerDeclared
    (g : CountertermLocalDensityBasisGate) : Prop :=
  g.nonlinearResidualClosureImported /\
  g.boundaryCountertermBibliographyChecked /\
  g.activeVariableBasisDeclared /\
  g.hBlockDeclared /\
  g.kBlockDeclared /\
  g.torsionPullbackBlockDeclared /\
  g.immirziBoundaryBlockDeclared /\
  g.z2OrientationBlockDeclared /\
  g.noNewCountertermFreedomDeclared /\
  g.observationalFitForbidden

def countertermLocalDensityBasisReady
    (g : CountertermLocalDensityBasisGate) : Prop :=
  countertermLocalDensityBasisLedgerDeclared g /\
  g.uniqueCountertermTransported /\
  g.localDensityBasisComplete /\
  g.lCtLocalExpansionDerived /\
  g.lCtReadyForDensityExpansionGate

theorem local_density_ready_requires_expansion
    (g : CountertermLocalDensityBasisGate)
    (hReady : countertermLocalDensityBasisReady g) :
    g.lCtLocalExpansionDerived := by
  exact hReady.right.right.right.left

end P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate
end JanusFormal
