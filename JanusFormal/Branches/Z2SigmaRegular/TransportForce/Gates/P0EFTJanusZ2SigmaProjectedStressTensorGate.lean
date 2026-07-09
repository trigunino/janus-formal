import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryVariationalDecompositionGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaBackgroundBibliographyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectedStressTensorGate

set_option autoImplicit false

structure Z2SigmaProjectedStressTensorGate where
  sigmaBoundaryVariationalPackageDeclared : Prop
  sigmaBoundaryNonlinearResidualClosed : Prop
  localBackgroundDerivationRequired : Prop
  inducedSigmaMetricDeclared : Prop
  boundaryActionVariationWithRespectToInducedMetricDeclared : Prop
  brownYorkLikeProjectionDeclared : Prop
  z2ProjectionToVisibleBackgroundDeclared : Prop
  projectedSigmaStressTensorDerived : Prop

def projectedStressTensorLockClosed
    (g : Z2SigmaProjectedStressTensorGate) : Prop :=
  g.sigmaBoundaryVariationalPackageDeclared /\
  g.sigmaBoundaryNonlinearResidualClosed /\
  g.localBackgroundDerivationRequired /\
  g.inducedSigmaMetricDeclared /\
  g.boundaryActionVariationWithRespectToInducedMetricDeclared /\
  g.brownYorkLikeProjectionDeclared /\
  g.z2ProjectionToVisibleBackgroundDeclared

theorem projected_stress_lock_derives_sigma_stress_tensor
    (g : Z2SigmaProjectedStressTensorGate)
    (hLock : projectedStressTensorLockClosed g)
    (hImplies : projectedStressTensorLockClosed g -> g.projectedSigmaStressTensorDerived) :
    g.projectedSigmaStressTensorDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaProjectedStressTensorGate
end JanusFormal
