import JanusFormal.P0EFTJanusZ2SigmaTangentNormalOrientationGate
import JanusFormal.P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaNormalMatterCurrentGate

set_option autoImplicit false

structure NormalMatterCurrentGate where
  matterCurrentBibliographyChecked : Prop
  noetherCurrentFormulaImported : Prop
  plusMinusMatterCurrentGateDeclared : Prop
  normalProjectionCriterionDeclared : Prop
  sigmaNormalsRequired : Prop
  z2ProjectedCurrentDeclared : Prop
  observationalFitForbidden : Prop
  plusMatterCurrentReady : Prop
  minusMatterCurrentReady : Prop
  sigmaNormalsReady : Prop
  z2ProjectedNormalCurrentReady : Prop
  noNormalMatterCurrentDerived : Prop

def normalMatterCurrentLedgerDeclared
    (g : NormalMatterCurrentGate) : Prop :=
  g.matterCurrentBibliographyChecked /\
  g.noetherCurrentFormulaImported /\
  g.plusMinusMatterCurrentGateDeclared /\
  g.normalProjectionCriterionDeclared /\
  g.sigmaNormalsRequired /\
  g.z2ProjectedCurrentDeclared /\
  g.observationalFitForbidden

def noNormalMatterCurrentReady
    (g : NormalMatterCurrentGate) : Prop :=
  normalMatterCurrentLedgerDeclared g /\
  g.plusMatterCurrentReady /\
  g.minusMatterCurrentReady /\
  g.sigmaNormalsReady /\
  g.z2ProjectedNormalCurrentReady /\
  g.noNormalMatterCurrentDerived

theorem no_normal_current_requires_sigma_normals
    (g : NormalMatterCurrentGate)
    (hReady : noNormalMatterCurrentReady g) :
    g.sigmaNormalsReady := by
  exact hReady.2.2.2.1

end P0EFTJanusZ2SigmaNormalMatterCurrentGate
end JanusFormal
