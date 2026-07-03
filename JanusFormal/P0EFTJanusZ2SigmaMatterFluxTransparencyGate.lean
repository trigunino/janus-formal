import JanusFormal.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
import JanusFormal.P0EFTJanusZ2SigmaNormalMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxTransparencyGate

set_option autoImplicit false

structure MatterFluxTransparencyGate where
  thinShellTransparencyBibliographyChecked : Prop
  noNormalMatterCurrentCriterionDeclared : Prop
  normalMatterCurrentGateDeclared : Prop
  projectedDiracNormalCurrentGateDeclared : Prop
  bulkStressNormalFluxCancellationGateDeclared : Prop
  bulkStressNormalProjectionCriterionDeclared : Prop
  sigmaAsGeometricThroatNotMatterPortalDeclared : Prop
  z2FluxCancellationCriterionDeclared : Prop
  observationalFitForbidden : Prop
  transparencySufficientConditionsDeclared : Prop
  noNormalMatterCurrentDerived : Prop
  bulkStressNormalProjectionZeroDerived : Prop
  z2FluxCancellationDerived : Prop
  activeSigmaTransparencyDerived : Prop

def transparencyCriteriaDeclared
    (g : MatterFluxTransparencyGate) : Prop :=
  g.thinShellTransparencyBibliographyChecked /\
  g.noNormalMatterCurrentCriterionDeclared /\
  g.normalMatterCurrentGateDeclared /\
  g.projectedDiracNormalCurrentGateDeclared /\
  g.bulkStressNormalFluxCancellationGateDeclared /\
  g.bulkStressNormalProjectionCriterionDeclared /\
  g.sigmaAsGeometricThroatNotMatterPortalDeclared /\
  g.z2FluxCancellationCriterionDeclared /\
  g.observationalFitForbidden /\
  g.transparencySufficientConditionsDeclared

def activeSigmaTransparencyReady
    (g : MatterFluxTransparencyGate) : Prop :=
  transparencyCriteriaDeclared g /\
  g.noNormalMatterCurrentDerived /\
  g.bulkStressNormalProjectionZeroDerived /\
  g.z2FluxCancellationDerived /\
  g.activeSigmaTransparencyDerived

theorem transparency_requires_no_normal_current
    (g : MatterFluxTransparencyGate)
    (hReady : activeSigmaTransparencyReady g) :
    g.noNormalMatterCurrentDerived := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaMatterFluxTransparencyGate
end JanusFormal
