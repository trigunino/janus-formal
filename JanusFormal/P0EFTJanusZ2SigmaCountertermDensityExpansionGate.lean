import JanusFormal.P0EFTJanusZ2SigmaCountertermRadialBlockGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermDensityExpansionGate

set_option autoImplicit false

structure CountertermDensityExpansionGate where
  sigmaCountertermUniquenessImported : Prop
  countertermCancelsNonlinearResidualImported : Prop
  densityExpansionProblemDeclared : Prop
  allowedVariablesDeclared : Prop
  noNewCountertermFreedomDeclared : Prop
  observationalFitForbidden : Prop
  explicitDensityExpansionRequired : Prop
  lCtExpandedInActiveVariables : Prop
  lCtUniquenessPreserved : Prop
  lCtReadyForRadialVariation : Prop

def countertermDensityExpansionLedgerDeclared
    (g : CountertermDensityExpansionGate) : Prop :=
  g.sigmaCountertermUniquenessImported /\
  g.countertermCancelsNonlinearResidualImported /\
  g.densityExpansionProblemDeclared /\
  g.allowedVariablesDeclared /\
  g.noNewCountertermFreedomDeclared /\
  g.observationalFitForbidden /\
  g.explicitDensityExpansionRequired

def countertermDensityExpansionReady
    (g : CountertermDensityExpansionGate) : Prop :=
  countertermDensityExpansionLedgerDeclared g /\
  g.lCtExpandedInActiveVariables /\
  g.lCtUniquenessPreserved /\
  g.lCtReadyForRadialVariation

theorem lct_ready_requires_expansion
    (g : CountertermDensityExpansionGate)
    (hReady : countertermDensityExpansionReady g) :
    g.lCtExpandedInActiveVariables := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaCountertermDensityExpansionGate
end JanusFormal
