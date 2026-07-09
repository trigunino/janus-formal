import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate

set_option autoImplicit false

structure CoupledRadiusFluxWellPosednessGate where
  coupledRadiusFluxSystemImported : Prop
  thinShellWellPosednessBibliographyChecked : Prop
  unknownSpaceDeclared : Prop
  equationMapDeclared : Prop
  boundaryConditionsDeclared : Prop
  regularityClassDeclared : Prop
  linearizedOperatorDeclared : Prop
  closureConditionsDeclared : Prop
  noIndependentFluxShortcut : Prop
  noObservationalRadiusFit : Prop
  localExistenceProved : Prop
  localUniquenessProved : Prop
  continuousDependenceProved : Prop
  constraintCompatibilityProved : Prop
  homogeneousGaugeModeFixed : Prop
  coupledSystemWellPosed : Prop

def wellPosednessLedgerDeclared
    (g : CoupledRadiusFluxWellPosednessGate) : Prop :=
  g.coupledRadiusFluxSystemImported /\
  g.thinShellWellPosednessBibliographyChecked /\
  g.unknownSpaceDeclared /\
  g.equationMapDeclared /\
  g.boundaryConditionsDeclared /\
  g.regularityClassDeclared /\
  g.linearizedOperatorDeclared /\
  g.closureConditionsDeclared /\
  g.noIndependentFluxShortcut /\
  g.noObservationalRadiusFit

def wellPosednessReady
    (g : CoupledRadiusFluxWellPosednessGate) : Prop :=
  wellPosednessLedgerDeclared g /\
  g.localExistenceProved /\
  g.localUniquenessProved /\
  g.continuousDependenceProved /\
  g.constraintCompatibilityProved /\
  g.homogeneousGaugeModeFixed /\
  g.coupledSystemWellPosed

theorem well_posedness_requires_local_existence
    (g : CoupledRadiusFluxWellPosednessGate)
    (hReady : wellPosednessReady g) :
    g.localExistenceProved := by
  exact hReady.2.1

theorem well_posedness_feeds_coupled_system_frontier
    (g : CoupledRadiusFluxWellPosednessGate)
    (hReady : wellPosednessReady g) :
    g.coupledSystemWellPosed := by
  exact hReady.2.2.2.2.2.2

end P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate
end JanusFormal
