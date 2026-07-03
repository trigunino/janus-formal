import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate
import JanusFormal.P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate

set_option autoImplicit false

structure CoupledRadiusFluxSystemGate where
  throatRadiusVariationalEquationImported : Prop
  matterFluxActiveProjectionImported : Prop
  matterFluxRadiusAcyclicityImported : Prop
  thinShellFluxBibliographyChecked : Prop
  coupledUnknownsDeclared : Prop
  coupledEquationsDeclared : Prop
  noIndependentFluxShortcutDeclared : Prop
  noObservationalRadiusFit : Prop
  eRSigmaEquationReady : Prop
  fZ2SigmaFunctionalDeclared : Prop
  embeddingDependenceRecorded : Prop
  closureConditionsDeclared : Prop
  coupledSystemWellPosed : Prop
  coupledSystemSolved : Prop
  rSigmaOfAReady : Prop
  activeFluxOfAReady : Prop
  matterFluxCanEnterRadiusSolution : Prop

def coupledRadiusFluxLedgerDeclared
    (g : CoupledRadiusFluxSystemGate) : Prop :=
  g.throatRadiusVariationalEquationImported /\
  g.matterFluxActiveProjectionImported /\
  g.matterFluxRadiusAcyclicityImported /\
  g.thinShellFluxBibliographyChecked /\
  g.coupledUnknownsDeclared /\
  g.coupledEquationsDeclared /\
  g.noIndependentFluxShortcutDeclared /\
  g.noObservationalRadiusFit

def coupledRadiusFluxSystemReady
    (g : CoupledRadiusFluxSystemGate) : Prop :=
  coupledRadiusFluxLedgerDeclared g /\
  g.eRSigmaEquationReady /\
  g.fZ2SigmaFunctionalDeclared /\
  g.embeddingDependenceRecorded /\
  g.closureConditionsDeclared /\
  g.coupledSystemWellPosed

def coupledRadiusFluxSolutionReady
    (g : CoupledRadiusFluxSystemGate) : Prop :=
  coupledRadiusFluxSystemReady g /\
  g.coupledSystemSolved /\
  g.rSigmaOfAReady /\
  g.activeFluxOfAReady /\
  g.matterFluxCanEnterRadiusSolution

theorem coupled_solution_required_before_flux_enters_radius
    (g : CoupledRadiusFluxSystemGate)
    (hReady : coupledRadiusFluxSolutionReady g) :
    g.coupledSystemSolved := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate
end JanusFormal
