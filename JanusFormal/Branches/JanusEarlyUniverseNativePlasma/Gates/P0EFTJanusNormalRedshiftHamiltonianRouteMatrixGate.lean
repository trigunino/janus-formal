import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31CoadjointRhoTransferAttemptGate

namespace JanusFormal
namespace P0EFTJanusNormalRedshiftHamiltonianRouteMatrixGate

set_option autoImplicit false

structure NormalRedshiftHamiltonianRouteMatrixGate where
  coadjointRhoAvailable : Prop
  PTSigmaBoundaryActionHamiltonianDerived : Prop
  boundaryModularHamiltonianDerived : Prop
  geometricThroatLengthOperatorSufficientAlone : Prop
  KKSMomentMapNormalGeneratorDerived : Prop
  empiricalOrderingRejected : Prop
  normalHamiltonianClosed : Prop

def routeMatrixAllowsClosure
    (g : NormalRedshiftHamiltonianRouteMatrixGate) : Prop :=
  g.coadjointRhoAvailable /\
  (
    g.PTSigmaBoundaryActionHamiltonianDerived \/
    g.boundaryModularHamiltonianDerived \/
    g.KKSMomentMapNormalGeneratorDerived
  ) /\
  g.empiricalOrderingRejected /\
  g.normalHamiltonianClosed

def routeMatrixFrontier
    (g : NormalRedshiftHamiltonianRouteMatrixGate) : Prop :=
  g.coadjointRhoAvailable /\
  Not g.PTSigmaBoundaryActionHamiltonianDerived /\
  Not g.boundaryModularHamiltonianDerived /\
  Not g.geometricThroatLengthOperatorSufficientAlone /\
  Not g.KKSMomentMapNormalGeneratorDerived /\
  g.empiricalOrderingRejected /\
  Not g.normalHamiltonianClosed

theorem no_action_or_modular_hamiltonian_blocks_normal_route_closure
    (g : NormalRedshiftHamiltonianRouteMatrixGate)
    (hFrontier : routeMatrixFrontier g) :
    Not (routeMatrixAllowsClosure g) := by
  intro h
  rcases h.2.1 with hAction | hModular | hKKS
  · exact hFrontier.2.1 hAction
  · exact hFrontier.2.2.1 hModular
  · exact hFrontier.2.2.2.2.1 hKKS

end P0EFTJanusNormalRedshiftHamiltonianRouteMatrixGate
end JanusFormal
