import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaTangentNormalOrientationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate

set_option autoImplicit false

structure ProjectedDiracNormalCurrentGate where
  thinShellFluxBibliographyChecked : Prop
  projectedDiracMatterCurrentGateDeclared : Prop
  tangentNormalOrientationGateDeclared : Prop
  plusNormalCurrentDeclared : Prop
  minusNormalCurrentDeclared : Prop
  z2ProjectedNormalCurrentDeclared : Prop
  noFitTransparencyDecision : Prop
  observationalFitForbidden : Prop
  projectedDiracMatterCurrentReady : Prop
  sigmaNormalsReady : Prop
  plusNormalCurrentReady : Prop
  minusNormalCurrentReady : Prop
  z2ProjectedNormalCurrentReady : Prop
  noNormalMatterCurrentDerived : Prop

def projectedDiracNormalCurrentLedgerDeclared
    (g : ProjectedDiracNormalCurrentGate) : Prop :=
  g.thinShellFluxBibliographyChecked /\
  g.projectedDiracMatterCurrentGateDeclared /\
  g.tangentNormalOrientationGateDeclared /\
  g.plusNormalCurrentDeclared /\
  g.minusNormalCurrentDeclared /\
  g.z2ProjectedNormalCurrentDeclared /\
  g.noFitTransparencyDecision /\
  g.observationalFitForbidden

def projectedDiracNormalCurrentReady
    (g : ProjectedDiracNormalCurrentGate) : Prop :=
  projectedDiracNormalCurrentLedgerDeclared g /\
  g.projectedDiracMatterCurrentReady /\
  g.sigmaNormalsReady /\
  g.plusNormalCurrentReady /\
  g.minusNormalCurrentReady /\
  g.z2ProjectedNormalCurrentReady

def noNormalDiracCurrentReady
    (g : ProjectedDiracNormalCurrentGate) : Prop :=
  projectedDiracNormalCurrentReady g /\ g.noNormalMatterCurrentDerived

theorem projected_normal_current_requires_sigma_normals
    (g : ProjectedDiracNormalCurrentGate)
    (hReady : projectedDiracNormalCurrentReady g) :
    g.sigmaNormalsReady := by
  exact hReady.2.2.1

end P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate
end JanusFormal
