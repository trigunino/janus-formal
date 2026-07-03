import JanusFormal.P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate
import JanusFormal.P0EFTJanusZ2SigmaMatterFluxTransparencyGate
import JanusFormal.P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaNormalMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxFrontierGate

set_option autoImplicit false

structure MatterFluxFrontierGate where
  routeDecisionGateImported : Prop
  transparencyGateImported : Prop
  activeProjectionGateImported : Prop
  normalMatterCurrentGateImported : Prop
  bulkStressFluxCancellationGateImported : Prop
  thinShellFluxBibliographyChecked : Prop
  noFitRoutePolicyDeclared : Prop
  transparencyCriteriaDeclared : Prop
  noNormalMatterCurrentReady : Prop
  bulkStressCancellationReady : Prop
  activeFluxProjectionReady : Prop
  routeDecisionReady : Prop
  matterFluxRadialBlockReduced : Prop

def matterFluxFrontierLedgerDeclared
    (g : MatterFluxFrontierGate) : Prop :=
  g.routeDecisionGateImported /\
  g.transparencyGateImported /\
  g.activeProjectionGateImported /\
  g.normalMatterCurrentGateImported /\
  g.bulkStressFluxCancellationGateImported /\
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
  g.routeDecisionReady /\
  g.matterFluxRadialBlockReduced

theorem matter_flux_frontier_requires_transparency_or_projection
    (g : MatterFluxFrontierGate)
    (hReady : matterFluxFrontierReady g) :
    matterFluxTransparencyPathReady g \/ matterFluxActiveProjectionPathReady g := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaMatterFluxFrontierGate
end JanusFormal
