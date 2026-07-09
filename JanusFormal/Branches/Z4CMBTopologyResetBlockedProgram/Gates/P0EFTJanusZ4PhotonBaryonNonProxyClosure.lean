import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PhotonBaryonIntegratorTarget
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4HierarchyCoefficientClosure

namespace JanusFormal
namespace P0EFTJanusZ4PhotonBaryonNonProxyClosure

set_option autoImplicit false

structure PhotonBaryonNonProxyClosure where
  soundSpeedCoefficientDerived : Prop
  baryonLoadingCoefficientDerived : Prop
  thomsonDragPairClosed : Prop
  z4MetricForcingInserted : Prop
  calibratedVisibilityInputRequired : Prop
  finiteBoltzmannStepProduced : Prop
  singleSectorLimitRecovered : Prop

def photonBaryonNonProxyClosureReady (p : PhotonBaryonNonProxyClosure) : Prop :=
  p.soundSpeedCoefficientDerived /\
  p.baryonLoadingCoefficientDerived /\
  p.thomsonDragPairClosed /\
  p.z4MetricForcingInserted /\
  p.calibratedVisibilityInputRequired /\
  p.finiteBoltzmannStepProduced /\
  p.singleSectorLimitRecovered

theorem nonproxy_closure_gives_finite_step
    (p : PhotonBaryonNonProxyClosure)
    (h : photonBaryonNonProxyClosureReady p) :
    p.finiteBoltzmannStepProduced := by
  exact h.right.right.right.right.right.left

theorem nonproxy_closure_recovers_single_sector_limit
    (p : PhotonBaryonNonProxyClosure)
    (h : photonBaryonNonProxyClosureReady p) :
    p.singleSectorLimitRecovered := by
  exact h.right.right.right.right.right.right

end P0EFTJanusZ4PhotonBaryonNonProxyClosure
end JanusFormal
