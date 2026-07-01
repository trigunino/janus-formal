import JanusFormal.P0EFTJanusZ4ObstructionWardIdentity

namespace JanusFormal
namespace P0EFTJanusZ4AnomalyCancellationTarget

set_option autoImplicit false

structure Z4AnomalyCancellationTarget where
  bulkAnomalyDeclared : Prop
  boundaryAnomalyDeclared : Prop
  measureAnomalyDeclared : Prop
  totalAnomalyIsChannelSum : Prop
  boundaryCancelsBulk : Prop
  measureAnomalyVanishes : Prop
  totalAnomalyVanishes : Prop
  determinantWeightCompatible : Prop
  nonlinearCurrentConservationDerived : Prop

def anomalyCancellationTargetReady (a : Z4AnomalyCancellationTarget) : Prop :=
  a.bulkAnomalyDeclared /\
  a.boundaryAnomalyDeclared /\
  a.measureAnomalyDeclared /\
  a.totalAnomalyIsChannelSum /\
  a.boundaryCancelsBulk /\
  a.measureAnomalyVanishes /\
  a.totalAnomalyVanishes /\
  a.determinantWeightCompatible

def anomalyCancellationPhysicalReady (a : Z4AnomalyCancellationTarget) : Prop :=
  anomalyCancellationTargetReady a /\
  a.nonlinearCurrentConservationDerived

theorem target_ready_gives_total_anomaly_zero
    (a : Z4AnomalyCancellationTarget)
    (h : anomalyCancellationTargetReady a) :
    a.totalAnomalyVanishes := by
  exact h.right.right.right.right.right.right.left

theorem anomaly_target_does_not_close_full_action
    (a : Z4AnomalyCancellationTarget)
    (_h : anomalyCancellationTargetReady a)
    (hMissing : Not a.nonlinearCurrentConservationDerived) :
    Not (anomalyCancellationPhysicalReady a) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4AnomalyCancellationTarget
end JanusFormal
