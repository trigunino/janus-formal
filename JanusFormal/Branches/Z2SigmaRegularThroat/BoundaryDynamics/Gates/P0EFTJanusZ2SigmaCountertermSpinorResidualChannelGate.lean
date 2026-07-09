import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBundleProjectionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate

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
  localMITReflectingProjectorReady : Prop
  normalCurrentZeroAlgebraReady : Prop
  boundarySpinorSatisfiesReflectingProjectorDerived : Prop
  conditionalReflectingProjectorResidualZero : Prop
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

def conditionalReflectingProjectorRouteAvailable
    (g : CountertermSpinorResidualChannelGate) : Prop :=
  countertermSpinorResidualChannelLedgerDeclared g /\
  g.localMITReflectingProjectorReady /\
  g.normalCurrentZeroAlgebraReady /\
  g.conditionalReflectingProjectorResidualZero

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

theorem reflecting_projector_route_still_requires_physical_boundary_condition
    (g : CountertermSpinorResidualChannelGate)
    (_hRoute : conditionalReflectingProjectorRouteAvailable g)
    (hPhysical : g.boundarySpinorSatisfiesReflectingProjectorDerived) :
    g.boundarySpinorSatisfiesReflectingProjectorDerived := by
  exact hPhysical

theorem local_projected_zero_coefficients_close_spinor_channel
    (g : CountertermSpinorResidualChannelGate)
    (hLedger : countertermSpinorResidualChannelLedgerDeclared g)
    (hRpsi : g.spinorResidualCoefficientExplicit)
    (hRpsibar : g.conjugateSpinorResidualCoefficientExplicit)
    (hBasis : g.spinorResidualInAllowedBasis)
    (hProjection : g.spinorResidualCompatibleWithProjection)
    (hOneForm : g.spinorResidualReadyForOneFormDecomposition) :
    countertermSpinorResidualChannelReady g := by
  exact And.intro hLedger
    (And.intro hRpsi
      (And.intro hRpsibar
        (And.intro hBasis
          (And.intro hProjection hOneForm))))

end P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate
end JanusFormal
