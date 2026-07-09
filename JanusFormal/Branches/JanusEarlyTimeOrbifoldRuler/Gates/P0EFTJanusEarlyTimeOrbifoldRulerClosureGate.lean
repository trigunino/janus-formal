import JanusFormal.Branches.NativeBAORulerContract.Gates.P0EFTJanusNativeBAORulerContractGate
import JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler.Gates.P0EFTJanusOrbifoldRedshiftMapRulerGate
import JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler.Gates.P0EFTJanusEarlyTimeSisterBranchRulerGate
import JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler.Gates.P0EFTJanusTopologicalSpectrumRulerGate
import JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler.Gates.P0EFTJanusProjectedPlasmaRulerGate

namespace JanusFormal
namespace P0EFTJanusEarlyTimeOrbifoldRulerClosureGate

set_option autoImplicit false

structure EarlyTimeOrbifoldRulerClosureGate where
  nativeBAOContractFormulated : Prop
  lateTimeBranchDoesNotReachDrag : Prop
  redshiftMapRouteBlocked : Prop
  sisterBranchRouteBlocked : Prop
  topologicalSpectrumRouteBlocked : Prop
  projectedPlasmaRouteBlocked : Prop
  noLCDMRdReuse : Prop
  noAlphaFitRepair : Prop
  nativeEarlyTimeRulerReady : Prop

def allRoutesAtCurrentBottom (g : EarlyTimeOrbifoldRulerClosureGate) : Prop :=
  g.nativeBAOContractFormulated /\
  g.lateTimeBranchDoesNotReachDrag /\
  g.redshiftMapRouteBlocked /\
  g.sisterBranchRouteBlocked /\
  g.topologicalSpectrumRouteBlocked /\
  g.projectedPlasmaRouteBlocked /\
  g.noLCDMRdReuse /\
  g.noAlphaFitRepair /\
  Not g.nativeEarlyTimeRulerReady

theorem current_bottom_blocks_native_bao_ruler
    (g : EarlyTimeOrbifoldRulerClosureGate)
    (h : allRoutesAtCurrentBottom g) :
    Not g.nativeEarlyTimeRulerReady := by
  exact h.2.2.2.2.2.2.2.2

end P0EFTJanusEarlyTimeOrbifoldRulerClosureGate
end JanusFormal
