import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate

set_option autoImplicit false

structure CountertermConnectionVariationTransportGate where
  coframeConnectionPullbackGateDeclared : Prop
  torsionPullbackOnSigmaGateDeclared : Prop
  holstNiehYanRadialBlockGateDeclared : Prop
  holstNiehYanConnectionVariationBibliographyChecked : Prop
  connectionVariationBasisDeclared : Prop
  fixedCoframeConnectionVariationBranchDeclared : Prop
  deltaOmegaToDeltaTorsionFormulaDeclared : Prop
  deltaTorsionToNiehYanVariationDeclared : Prop
  sigmaPullbackCommutationDeclared : Prop
  fixedEmbeddingConnectionPullbackVariationGateDeclared : Prop
  z2OrientationTransportDeclared : Prop
  noFittedTransportCoefficient : Prop
  fixedEmbeddingCommutationSubchannelReady : Prop
  sigmaPullbackReady : Prop
  deltaOmegaToDeltaTorsionFormulaProved : Prop
  niehYanVariationTransportProved : Prop
  connectionVariationTransportReady : Prop

def countertermConnectionVariationTransportLedgerDeclared
    (g : CountertermConnectionVariationTransportGate) : Prop :=
  g.coframeConnectionPullbackGateDeclared /\
  g.torsionPullbackOnSigmaGateDeclared /\
  g.holstNiehYanRadialBlockGateDeclared /\
  g.holstNiehYanConnectionVariationBibliographyChecked /\
  g.connectionVariationBasisDeclared /\
  g.fixedCoframeConnectionVariationBranchDeclared /\
  g.deltaOmegaToDeltaTorsionFormulaDeclared /\
  g.deltaTorsionToNiehYanVariationDeclared /\
  g.sigmaPullbackCommutationDeclared /\
  g.fixedEmbeddingConnectionPullbackVariationGateDeclared /\
  g.z2OrientationTransportDeclared /\
  g.noFittedTransportCoefficient

def countertermConnectionVariationTransportReady
    (g : CountertermConnectionVariationTransportGate) : Prop :=
  countertermConnectionVariationTransportLedgerDeclared g /\
  g.sigmaPullbackReady /\
  g.deltaOmegaToDeltaTorsionFormulaProved /\
  g.niehYanVariationTransportProved /\
  g.connectionVariationTransportReady

theorem connection_transport_ready_requires_delta_torsion_formula
    (g : CountertermConnectionVariationTransportGate)
    (hReady : countertermConnectionVariationTransportReady g) :
    g.deltaOmegaToDeltaTorsionFormulaProved := by
  exact hReady.right.right.left

theorem fixed_commutation_subchannel_alone_does_not_close_connection_transport
    (g : CountertermConnectionVariationTransportGate)
    (_hSubchannel : g.fixedEmbeddingCommutationSubchannelReady)
    (hMissing : Not g.sigmaPullbackReady) :
    Not (countertermConnectionVariationTransportReady g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate
end JanusFormal
