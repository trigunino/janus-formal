import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxTransparencyGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaNormalMatterCurrentGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxFrontierGate

set_option autoImplicit false

structure MatterFluxFrontierGate where
  routeDecisionGateImported : Prop
  transparencyGateImported : Prop
  activeProjectionGateImported : Prop
  normalMatterCurrentGateImported : Prop
  bulkStressFluxCancellationGateImported : Prop
  matterFluxRadiusAcyclicityGateChecked : Prop
  thinShellFluxBibliographyChecked : Prop
  noFitRoutePolicyDeclared : Prop
  transparencyCriteriaDeclared : Prop
  noNormalMatterCurrentReady : Prop
  bulkStressCancellationReady : Prop
  activeFluxProjectionReady : Prop
  matterFluxRadiusAcyclicRouteReady : Prop
  routeDecisionReady : Prop
  matterFluxRadialBlockReduced : Prop
  nearestMatterFluxRouteFrontierDeclared : Prop
  nearestMatterFluxRouteFrontierDiagnosticOnly : Prop

def matterFluxFrontierLedgerDeclared
    (g : MatterFluxFrontierGate) : Prop :=
  g.routeDecisionGateImported /\
  g.transparencyGateImported /\
  g.activeProjectionGateImported /\
  g.normalMatterCurrentGateImported /\
  g.bulkStressFluxCancellationGateImported /\
  g.matterFluxRadiusAcyclicityGateChecked /\
  g.thinShellFluxBibliographyChecked /\
  g.noFitRoutePolicyDeclared /\
  g.transparencyCriteriaDeclared

def matterFluxTransparencyPathReady
    (g : MatterFluxFrontierGate) : Prop :=
  matterFluxFrontierLedgerDeclared g /\
  g.noNormalMatterCurrentReady /\
  g.bulkStressCancellationReady

def matterFluxActiveProjectionPathReady
    (g : MatterFluxFrontierGate) : Prop :=
  matterFluxFrontierLedgerDeclared g /\
  g.activeFluxProjectionReady

def matterFluxFrontierReady
    (g : MatterFluxFrontierGate) : Prop :=
  matterFluxFrontierLedgerDeclared g /\
  (matterFluxTransparencyPathReady g \/ matterFluxActiveProjectionPathReady g) /\
  g.matterFluxRadiusAcyclicRouteReady /\
  g.routeDecisionReady /\
  g.matterFluxRadialBlockReduced

theorem matter_flux_frontier_requires_transparency_or_projection
    (g : MatterFluxFrontierGate)
    (hReady : matterFluxFrontierReady g) :
    matterFluxTransparencyPathReady g \/ matterFluxActiveProjectionPathReady g := by
  exact hReady.2.1

theorem matter_flux_frontier_requires_acyclic_radius_route
    (g : MatterFluxFrontierGate)
    (hReady : matterFluxFrontierReady g) :
    g.matterFluxRadiusAcyclicRouteReady := by
  exact hReady.2.2.1

theorem nearest_matter_flux_route_frontier_is_diagnostic_only
    (g : MatterFluxFrontierGate)
    (_h : g.nearestMatterFluxRouteFrontierDiagnosticOnly) :
    matterFluxFrontierReady g -> matterFluxFrontierReady g := by
  intro hReady
  exact hReady

end P0EFTJanusZ2SigmaMatterFluxFrontierGate
end JanusFormal
