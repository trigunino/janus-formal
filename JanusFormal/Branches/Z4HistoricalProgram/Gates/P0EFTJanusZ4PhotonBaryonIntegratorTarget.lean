import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4PhotonBaryonSourceClosure

namespace JanusFormal
namespace P0EFTJanusZ4PhotonBaryonIntegratorTarget

set_option autoImplicit false

structure PhotonBaryonIntegratorTarget where
  rkStateDeclared : Prop
  z4MetricSourcesInserted : Prop
  thomsonDragInserted : Prop
  finiteTrajectoryProduced : Prop
  singleSectorLimitStable : Prop
  calibratedBoltzmannIntegratorExecuted : Prop

def photonBaryonIntegratorReady (p : PhotonBaryonIntegratorTarget) : Prop :=
  p.rkStateDeclared /\
  p.z4MetricSourcesInserted /\
  p.thomsonDragInserted /\
  p.finiteTrajectoryProduced /\
  p.singleSectorLimitStable

def photonBaryonHierarchyNonProxyReady (p : PhotonBaryonIntegratorTarget) : Prop :=
  photonBaryonIntegratorReady p /\
  p.calibratedBoltzmannIntegratorExecuted

theorem integrator_target_requires_finite_trajectory
    (p : PhotonBaryonIntegratorTarget)
    (h : photonBaryonIntegratorReady p) :
    p.finiteTrajectoryProduced := by
  exact h.right.right.right.left

theorem integrator_target_does_not_execute_boltzmann
    (p : PhotonBaryonIntegratorTarget)
    (_h : photonBaryonIntegratorReady p)
    (hMissing : Not p.calibratedBoltzmannIntegratorExecuted) :
    Not (photonBaryonHierarchyNonProxyReady p) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4PhotonBaryonIntegratorTarget
end JanusFormal
