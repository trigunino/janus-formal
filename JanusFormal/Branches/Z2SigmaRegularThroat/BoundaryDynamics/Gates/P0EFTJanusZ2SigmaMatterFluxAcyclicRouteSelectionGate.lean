import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxAcyclicRouteSelectionGate

set_option autoImplicit false

structure MatterFluxAcyclicRouteSelectionGate where
  activeCoreZ2Sigma : Prop
  transparencyDependsOnUnknownEmbedding : Prop
  transparencyAcyclicReady : Prop
  activeSigmaTransparencyReady : Prop
  coupledRadiusFluxSystemReady : Prop
  coupledRadiusFluxSolutionReady : Prop
  independentFluxShortcutForbidden : Prop
  observationalRadiusFitForbidden : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4Forbidden : Prop
  gatePassed : Prop

def transparencyRouteReady (g : MatterFluxAcyclicRouteSelectionGate) : Prop :=
  g.transparencyAcyclicReady /\
  g.activeSigmaTransparencyReady /\
  Not g.transparencyDependsOnUnknownEmbedding

def coupledRouteReady (g : MatterFluxAcyclicRouteSelectionGate) : Prop :=
  g.coupledRadiusFluxSystemReady /\ g.coupledRadiusFluxSolutionReady

def ready (g : MatterFluxAcyclicRouteSelectionGate) : Prop :=
  g.activeCoreZ2Sigma /\
  (transparencyRouteReady g \/ coupledRouteReady g) /\
  g.independentFluxShortcutForbidden /\
  g.observationalRadiusFitForbidden /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4Forbidden

theorem transparency_route_requires_embedding_independence
    (g : MatterFluxAcyclicRouteSelectionGate)
    (h : transparencyRouteReady g) :
    Not g.transparencyDependsOnUnknownEmbedding := by
  exact h.2.2

theorem selected_route_requires_no_independent_flux_shortcut
    (g : MatterFluxAcyclicRouteSelectionGate)
    (h : ready g) :
    g.independentFluxShortcutForbidden := by
  exact h.2.2.1

end P0EFTJanusZ2SigmaMatterFluxAcyclicRouteSelectionGate
end JanusFormal
