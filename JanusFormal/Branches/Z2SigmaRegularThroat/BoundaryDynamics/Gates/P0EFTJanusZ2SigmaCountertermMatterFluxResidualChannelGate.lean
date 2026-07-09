import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBulkStressOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGate

set_option autoImplicit false

structure CountertermMatterFluxResidualChannelGate where
  matterFluxRadialBlockGateDeclared : Prop
  matterFluxActiveProjectionGateDeclared : Prop
  bulkStressOfAGateDeclared : Prop
  bulkStressNormalFluxCancellationGateDeclared : Prop
  matterFluxBoundaryVariationBibliographyChecked : Prop
  normalTangentFluxFormulaDeclared : Prop
  z2FluxOrientationDeclared : Prop
  activeFluxOfADeclared : Prop
  noFittedMatterResidualCoefficient : Prop
  matterResidualCoefficientExplicit : Prop
  matterResidualInAllowedBasis : Prop
  matterResidualReadyForOneFormDecomposition : Prop

def countertermMatterFluxResidualChannelLedgerDeclared
    (g : CountertermMatterFluxResidualChannelGate) : Prop :=
  g.matterFluxRadialBlockGateDeclared /\
  g.matterFluxActiveProjectionGateDeclared /\
  g.bulkStressOfAGateDeclared /\
  g.bulkStressNormalFluxCancellationGateDeclared /\
  g.matterFluxBoundaryVariationBibliographyChecked /\
  g.normalTangentFluxFormulaDeclared /\
  g.z2FluxOrientationDeclared /\
  g.activeFluxOfADeclared /\
  g.noFittedMatterResidualCoefficient

def countertermMatterFluxResidualChannelReady
    (g : CountertermMatterFluxResidualChannelGate) : Prop :=
  countertermMatterFluxResidualChannelLedgerDeclared g /\
  g.matterResidualCoefficientExplicit /\
  g.matterResidualInAllowedBasis /\
  g.matterResidualReadyForOneFormDecomposition

theorem matter_flux_channel_ready_requires_explicit_coefficient
    (g : CountertermMatterFluxResidualChannelGate)
    (hReady : countertermMatterFluxResidualChannelReady g) :
    g.matterResidualCoefficientExplicit := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGate
end JanusFormal
