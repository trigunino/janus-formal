import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate

set_option autoImplicit false

structure MatterFluxRouteDecisionGate where
  thinShellFluxConservationBibliographyChecked : Prop
  transparencyRouteDeclared : Prop
  activeProjectionRouteDeclared : Prop
  routeExhaustiveForRadialBlock : Prop
  routeChoiceByFitForbidden : Prop
  transparencyDerived : Prop
  activeFluxProjectionReady : Prop
  matterFluxRouteDecided : Prop
  matterFluxRadialReductionAllowed : Prop

def matterFluxRouteLedgerDeclared
    (g : MatterFluxRouteDecisionGate) : Prop :=
  g.thinShellFluxConservationBibliographyChecked /\
  g.transparencyRouteDeclared /\
  g.activeProjectionRouteDeclared /\
  g.routeExhaustiveForRadialBlock /\
  g.routeChoiceByFitForbidden

def matterFluxRouteDecisionReady
    (g : MatterFluxRouteDecisionGate) : Prop :=
  matterFluxRouteLedgerDeclared g /\
  (g.transparencyDerived \/ g.activeFluxProjectionReady) /\
  g.matterFluxRouteDecided /\
  g.matterFluxRadialReductionAllowed

theorem matter_flux_route_requires_transparency_or_projection
    (g : MatterFluxRouteDecisionGate)
    (hReady : matterFluxRouteDecisionReady g) :
    g.transparencyDerived \/ g.activeFluxProjectionReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate
end JanusFormal
