import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryVariationalDecompositionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFermionRouteSelectionGate

set_option autoImplicit false

structure FermionRouteSelectionGate where
  fermionRouteBibliographyChecked : Prop
  sigmaSpinorVariationChannelImported : Prop
  diracGasRouteSelectedFromAction : Prop
  weyssenhoffRouteMarkedCoarseGrainingOnly : Prop
  noFluidRouteChosenByFit : Prop
  observationalFitForbidden : Prop
  routeSelectionReady : Prop

def fermionRouteLedgerDeclared
    (g : FermionRouteSelectionGate) : Prop :=
  g.fermionRouteBibliographyChecked /\
  g.sigmaSpinorVariationChannelImported /\
  g.diracGasRouteSelectedFromAction /\
  g.weyssenhoffRouteMarkedCoarseGrainingOnly /\
  g.noFluidRouteChosenByFit /\
  g.observationalFitForbidden

def fermionRouteSelectionReady
    (g : FermionRouteSelectionGate) : Prop :=
  fermionRouteLedgerDeclared g /\
  g.routeSelectionReady

theorem selected_route_is_dirac_if_ready
    (g : FermionRouteSelectionGate)
    (hReady : fermionRouteSelectionReady g) :
    g.diracGasRouteSelectedFromAction := by
  exact hReady.1.2.2.1

end P0EFTJanusZ2SigmaFermionRouteSelectionGate
end JanusFormal
