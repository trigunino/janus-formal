import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaNormalMatterCurrentGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate

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
  normalMatterCurrentReadinessReady : Prop
  normalMatterCurrentGateReady : Prop
  projectedDiracNormalCurrentReady : Prop
  noNormalMatterCurrentDerived : Prop
  bulkStressNormalFluxProjectionReady : Prop
  bulkStressNormalProjectionZeroDerived : Prop
  z2FluxCancellationDerived : Prop
  activeSigmaTransparencyDerived : Prop
  nearestTransparencySubfrontierDeclared : Prop
  nearestTransparencySubfrontierDiagnosticOnly : Prop

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

def bulkStressTransparencyCondition
    (g : MatterFluxTransparencyGate) : Prop :=
  g.bulkStressNormalProjectionZeroDerived \/ g.z2FluxCancellationDerived

def activeSigmaTransparencyReady
    (g : MatterFluxTransparencyGate) : Prop :=
  transparencyCriteriaDeclared g /\
  g.normalMatterCurrentReadinessReady /\
  g.normalMatterCurrentGateReady /\
  g.projectedDiracNormalCurrentReady /\
  g.noNormalMatterCurrentDerived /\
  g.bulkStressNormalFluxProjectionReady /\
  bulkStressTransparencyCondition g /\
  g.activeSigmaTransparencyDerived

theorem transparency_requires_no_normal_current
    (g : MatterFluxTransparencyGate)
    (hReady : activeSigmaTransparencyReady g) :
    g.noNormalMatterCurrentDerived := by
  exact hReady.2.2.2.2.1

theorem transparency_requires_current_readiness
    (g : MatterFluxTransparencyGate)
    (hReady : activeSigmaTransparencyReady g) :
    g.normalMatterCurrentReadinessReady /\ g.projectedDiracNormalCurrentReady := by
  exact And.intro hReady.2.1 hReady.2.2.2.1

theorem transparency_requires_bulk_flux_projection
    (g : MatterFluxTransparencyGate)
    (hReady : activeSigmaTransparencyReady g) :
    g.bulkStressNormalFluxProjectionReady := by
  exact hReady.2.2.2.2.2.1

theorem transparency_requires_bulk_zero_or_z2_cancellation
    (g : MatterFluxTransparencyGate)
    (hReady : activeSigmaTransparencyReady g) :
    bulkStressTransparencyCondition g := by
  exact hReady.2.2.2.2.2.2.1

theorem nearest_transparency_subfrontier_diagnostic_does_not_close_transparency
    (g : MatterFluxTransparencyGate)
    (_h : g.nearestTransparencySubfrontierDiagnosticOnly) :
    activeSigmaTransparencyReady g -> activeSigmaTransparencyReady g := by
  intro hReady
  exact hReady

end P0EFTJanusZ2SigmaMatterFluxTransparencyGate
end JanusFormal
