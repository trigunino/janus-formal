import JanusFormal.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
import JanusFormal.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate
import JanusFormal.P0EFTJanusZ2SigmaSpinorBundleProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate

set_option autoImplicit false

structure CountertermSpinorResidualChannelGate where
  boundarySpinorRestrictionGateDeclared : Prop
  spinorBoundaryProjectionMapGateDeclared : Prop
  spinorBundleProjectionGateDeclared : Prop
  projectedDiracActionReductionGateDeclared : Prop
  diracBoundaryVariationBibliographyChecked : Prop
  spinorVariationBasisDeclared : Prop
  projectedSpinorVariationTransportDeclared : Prop
  z2PinPhasePolicyDeclared : Prop
  noFittedSpinorResidualCoefficient : Prop
  spinorResidualCoefficientExplicit : Prop
  conjugateSpinorResidualCoefficientExplicit : Prop
  spinorResidualInAllowedBasis : Prop
  spinorResidualCompatibleWithProjection : Prop
  spinorResidualReadyForOneFormDecomposition : Prop

def countertermSpinorResidualChannelLedgerDeclared
    (g : CountertermSpinorResidualChannelGate) : Prop :=
  g.boundarySpinorRestrictionGateDeclared /\
  g.spinorBoundaryProjectionMapGateDeclared /\
  g.spinorBundleProjectionGateDeclared /\
  g.projectedDiracActionReductionGateDeclared /\
  g.diracBoundaryVariationBibliographyChecked /\
  g.spinorVariationBasisDeclared /\
  g.projectedSpinorVariationTransportDeclared /\
  g.z2PinPhasePolicyDeclared /\
  g.noFittedSpinorResidualCoefficient

def countertermSpinorResidualChannelReady
    (g : CountertermSpinorResidualChannelGate) : Prop :=
  countertermSpinorResidualChannelLedgerDeclared g /\
  g.spinorResidualCoefficientExplicit /\
  g.conjugateSpinorResidualCoefficientExplicit /\
  g.spinorResidualInAllowedBasis /\
  g.spinorResidualCompatibleWithProjection /\
  g.spinorResidualReadyForOneFormDecomposition

theorem spinor_channel_ready_requires_projected_residual
    (g : CountertermSpinorResidualChannelGate)
    (hReady : countertermSpinorResidualChannelReady g) :
    g.spinorResidualCompatibleWithProjection := by
  exact hReady.right.right.right.right.left

end P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate
end JanusFormal
