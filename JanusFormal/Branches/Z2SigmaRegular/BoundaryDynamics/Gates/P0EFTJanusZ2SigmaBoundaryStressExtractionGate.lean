import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryVariationalDecompositionGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBoundaryStressExtractionGate

set_option autoImplicit false

structure Z2SigmaBoundaryStressExtractionGate where
  fullBoundaryActionClosedOnSigma : Prop
  inducedMetricVariationDeclared : Prop
  cartanGHYContributionDeclared : Prop
  holstNiehYanContributionDeclared : Prop
  matterFluxContributionDeclared : Prop
  tunnelJunctionContributionDeclared : Prop
  countertermContributionDeclared : Prop
  tEffABExtractionFormulaReady : Prop
  tEffABComponentReductionReady : Prop
  tEffABReadyForFLRWProjection : Prop

def boundaryStressExtractionFormulaClosed
    (g : Z2SigmaBoundaryStressExtractionGate) : Prop :=
  g.fullBoundaryActionClosedOnSigma /\
  g.inducedMetricVariationDeclared /\
  g.cartanGHYContributionDeclared /\
  g.holstNiehYanContributionDeclared /\
  g.matterFluxContributionDeclared /\
  g.tunnelJunctionContributionDeclared /\
  g.countertermContributionDeclared /\
  g.tEffABExtractionFormulaReady

def boundaryStressReadyForFLRW
    (g : Z2SigmaBoundaryStressExtractionGate) : Prop :=
  boundaryStressExtractionFormulaClosed g /\
  g.tEffABComponentReductionReady /\
  g.tEffABReadyForFLRWProjection

theorem flrw_stress_requires_component_reduction
    (g : Z2SigmaBoundaryStressExtractionGate)
    (hReady : boundaryStressReadyForFLRW g) :
    g.tEffABComponentReductionReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaBoundaryStressExtractionGate
end JanusFormal
