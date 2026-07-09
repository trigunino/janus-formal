import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PhotonBaryonHierarchyTarget
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarConservationIdentity

namespace JanusFormal
namespace P0EFTJanusZ4PhotonBaryonSourceClosure

set_option autoImplicit false

structure PhotonBaryonSourceClosure where
  photonMetricSourceProjectedFromZ4 : Prop
  baryonMetricSourceProjectedFromZ4 : Prop
  thomsonDragPairAntisymmetric : Prop
  baryonLoadingUsed : Prop
  singleSectorLimitRecoversStandardHierarchy : Prop
  coefficientsFromFullZ4Action : Prop

def photonBaryonSourceClosureReady (p : PhotonBaryonSourceClosure) : Prop :=
  p.photonMetricSourceProjectedFromZ4 /\
  p.baryonMetricSourceProjectedFromZ4 /\
  p.thomsonDragPairAntisymmetric /\
  p.baryonLoadingUsed /\
  p.singleSectorLimitRecoversStandardHierarchy

def photonBaryonNonProxyReady (p : PhotonBaryonSourceClosure) : Prop :=
  photonBaryonSourceClosureReady p /\
  p.coefficientsFromFullZ4Action

theorem source_closure_keeps_thomson_internal
    (p : PhotonBaryonSourceClosure)
    (h : photonBaryonSourceClosureReady p) :
    p.thomsonDragPairAntisymmetric := by
  exact h.right.right.left

theorem source_closure_does_not_replace_action_coefficients
    (p : PhotonBaryonSourceClosure)
    (_h : photonBaryonSourceClosureReady p)
    (hMissing : Not p.coefficientsFromFullZ4Action) :
    Not (photonBaryonNonProxyReady p) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4PhotonBaryonSourceClosure
end JanusFormal
