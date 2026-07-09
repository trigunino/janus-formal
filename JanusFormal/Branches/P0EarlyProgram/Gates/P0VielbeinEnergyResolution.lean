import JanusFormal.Branches.P0EarlyProgram.Gates.P0OrbifoldProjectionGuards
import JanusFormal.Branches.P0EarlyProgram.Gates.P0OrbifoldActionCandidate

namespace JanusFormal
namespace P0VielbeinEnergyResolution

open P0OrbifoldProjectionGuards

set_option autoImplicit false

structure VielbeinSplitData (Vielbein Metric : Type) where
  globalVielbein : Vielbein
  plusVielbein : Vielbein
  minusVielbein : Vielbein
  plusMetric : Metric
  minusMetric : Metric
  z2ActsOnVielbein : Prop
  metricsInducedFromVielbein : Prop
  plusLorentzian : Prop
  minusLorentzian : Prop
  plusNondegenerate : Prop
  minusNondegenerate : Prop
  positiveVolumeBarrier : Prop

def vielbeinMetricClosure
    {Vielbein Metric : Type}
    (d : VielbeinSplitData Vielbein Metric) : Prop :=
  d.z2ActsOnVielbein /\
  d.metricsInducedFromVielbein /\
  d.plusLorentzian /\
  d.minusLorentzian /\
  d.plusNondegenerate /\
  d.minusNondegenerate /\
  d.positiveVolumeBarrier

def projectionGuardFromVielbein
    {Vielbein Metric : Type}
    (d : VielbeinSplitData Vielbein Metric) :
    Z2MetricProjectionData Metric :=
  { globalTensor := d.plusMetric
    evenProjection := d.plusMetric
    oddProjection := d.minusMetric
    hasEvenOddZ2Split := d.z2ActsOnVielbein
    timeReversalSymmetric := True
    evenProjectionNondegenerate := d.plusNondegenerate
    oddProjectionNondegenerate := d.minusNondegenerate
    negativeMassEnergyOrientation := False }

theorem vielbein_closure_gives_projection_nondegeneracy
    {Vielbein Metric : Type}
    (d : VielbeinSplitData Vielbein Metric)
    (h : vielbeinMetricClosure d) :
    evenOddNondegeneracyObligation (projectionGuardFromVielbein d) := by
  exact ⟨h.right.right.right.right.left, h.right.right.right.right.right.left⟩

theorem volume_barrier_alone_does_not_give_lorentzian_signature
    :
    Not (forall (Vielbein Metric : Type) (d : VielbeinSplitData Vielbein Metric),
      d.positiveVolumeBarrier -> d.minusLorentzian) := by
  intro h
  let bad : VielbeinSplitData Unit Unit :=
    { globalVielbein := ()
      plusVielbein := ()
      minusVielbein := ()
      plusMetric := ()
      minusMetric := ()
      z2ActsOnVielbein := True
      metricsInducedFromVielbein := True
      plusLorentzian := True
      minusLorentzian := False
      plusNondegenerate := True
      minusNondegenerate := True
      positiveVolumeBarrier := True }
  exact h Unit Unit bad trivial

structure QuantumEnergyOrientationData where
  timeReversalAntiunitary : Prop
  cptCompatible : Prop
  extendedPoincareRepresentation : Prop
  negativeEnergyBranchSelected : Prop
  vacuumStabilityControlled : Prop

def negativeSectorEnergyClosed (q : QuantumEnergyOrientationData) : Prop :=
  q.timeReversalAntiunitary /\
  q.cptCompatible /\
  q.extendedPoincareRepresentation /\
  q.negativeEnergyBranchSelected /\
  q.vacuumStabilityControlled

theorem quantum_energy_closure_gives_negative_orientation
    (q : QuantumEnergyOrientationData)
    (h : negativeSectorEnergyClosed q) :
    q.negativeEnergyBranchSelected := by
  exact h.right.right.right.left

theorem antiunitary_time_reversal_alone_not_enough
    :
    Not (forall q : QuantumEnergyOrientationData,
      q.timeReversalAntiunitary -> q.negativeEnergyBranchSelected) := by
  intro h
  let bad : QuantumEnergyOrientationData :=
    { timeReversalAntiunitary := True
      cptCompatible := True
      extendedPoincareRepresentation := False
      negativeEnergyBranchSelected := False
      vacuumStabilityControlled := True }
  exact h bad trivial

structure VielbeinEnergyResolution (Vielbein Metric : Type) where
  vielbeinData : VielbeinSplitData Vielbein Metric
  energyData : QuantumEnergyOrientationData

def resolutionClosed
    {Vielbein Metric : Type}
    (r : VielbeinEnergyResolution Vielbein Metric) : Prop :=
  vielbeinMetricClosure r.vielbeinData /\
  negativeSectorEnergyClosed r.energyData

theorem resolution_closes_projection_guards
    {Vielbein Metric : Type}
    (r : VielbeinEnergyResolution Vielbein Metric)
    (h : resolutionClosed r) :
    evenOddNondegeneracyObligation
      (projectionGuardFromVielbein r.vielbeinData) /\
    r.energyData.negativeEnergyBranchSelected := by
  exact
    ⟨vielbein_closure_gives_projection_nondegeneracy r.vielbeinData h.left,
      quantum_energy_closure_gives_negative_orientation r.energyData h.right⟩

end P0VielbeinEnergyResolution
end JanusFormal
