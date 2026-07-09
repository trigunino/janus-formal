import JanusFormal.Branches.P0EarlyProgram.Gates.P0OrbifoldActionProgram

namespace JanusFormal
namespace P0OrbifoldProjectionGuards

set_option autoImplicit false

structure Z2MetricProjectionData (Metric : Type) where
  globalTensor : Metric
  evenProjection : Metric
  oddProjection : Metric
  hasEvenOddZ2Split : Prop
  timeReversalSymmetric : Prop
  evenProjectionNondegenerate : Prop
  oddProjectionNondegenerate : Prop
  negativeMassEnergyOrientation : Prop

def evenOddNondegeneracyObligation
    {Metric : Type}
    (d : Z2MetricProjectionData Metric) : Prop :=
  d.evenProjectionNondegenerate /\ d.oddProjectionNondegenerate

def negativeEnergyOrientationObligation
    {Metric : Type}
    (d : Z2MetricProjectionData Metric) : Prop :=
  d.negativeMassEnergyOrientation

theorem z2_projection_of_global_tensor_does_not_imply_nondegeneracy :
    ¬ (forall (Metric : Type) (d : Z2MetricProjectionData Metric),
      d.hasEvenOddZ2Split -> evenOddNondegeneracyObligation d) := by
  intro h
  let bad : Z2MetricProjectionData Unit := {
    globalTensor := ()
    evenProjection := ()
    oddProjection := ()
    hasEvenOddZ2Split := True
    timeReversalSymmetric := True
    evenProjectionNondegenerate := False
    oddProjectionNondegenerate := True
    negativeMassEnergyOrientation := True
  }
  have hSplit : bad.hasEvenOddZ2Split := trivial
  have hBad : evenOddNondegeneracyObligation bad := h Unit bad hSplit
  exact hBad.left

theorem time_reversal_alone_does_not_imply_negative_energy_orientation :
    ¬ (forall (Metric : Type) (d : Z2MetricProjectionData Metric),
      d.timeReversalSymmetric -> negativeEnergyOrientationObligation d) := by
  intro h
  let bad : Z2MetricProjectionData Unit := {
    globalTensor := ()
    evenProjection := ()
    oddProjection := ()
    hasEvenOddZ2Split := True
    timeReversalSymmetric := True
    evenProjectionNondegenerate := True
    oddProjectionNondegenerate := True
    negativeMassEnergyOrientation := False
  }
  have hTR : bad.timeReversalSymmetric := trivial
  have hBad : negativeEnergyOrientationObligation bad :=
    h Unit bad hTR
  exact hBad

theorem nondegeneracy_and_energy_orientation_are_independent :
    ¬ (forall (Metric : Type) (d : Z2MetricProjectionData Metric),
      d.timeReversalSymmetric -> evenOddNondegeneracyObligation d -> negativeEnergyOrientationObligation d) := by
  intro h
  let bad : Z2MetricProjectionData Unit := {
    globalTensor := ()
    evenProjection := ()
    oddProjection := ()
    hasEvenOddZ2Split := True
    timeReversalSymmetric := True
    evenProjectionNondegenerate := True
    oddProjectionNondegenerate := True
    negativeMassEnergyOrientation := False
  }
  have hTR : bad.timeReversalSymmetric := trivial
  have hNondeg : evenOddNondegeneracyObligation bad :=
    And.intro trivial trivial
  have hBad : negativeEnergyOrientationObligation bad :=
    h Unit bad hTR hNondeg
  exact hBad

end P0OrbifoldProjectionGuards
end JanusFormal
