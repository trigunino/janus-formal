import Mathlib

namespace JanusFormal.P0EFTJanusOneLoopAnomalousDimension

set_option autoImplicit false

structure OneLoopMSWavefunctionData where
  poleResidue : ℝ
  anomalousDimensionContribution : ℝ
  oddDimensionalIntegralAudit : poleResidue = 0
  anomalousDimensionFromPole : anomalousDimensionContribution = poleResidue

/-- Once the one-loop integer-power bubble audit gives no MS pole, the
one-loop wavefunction anomalous dimension vanishes. -/
theorem one_loop_ms_anomalous_dimension_vanishes
    (s : OneLoopMSWavefunctionData) :
    s.anomalousDimensionContribution = 0 := by
  rw [s.anomalousDimensionFromPole, s.oddDimensionalIntegralAudit]

structure AnomalousDimensionClosureStatus where
  oneLoopNonLLPoleExcluded : Prop
  twoLoopNonLLCompositeInsertionComputed : Prop
  llCompositeInsertionComputed : Prop
  operatorMixingMatrixDiagonalized : Prop

def anomalousDimensionClosed (s : AnomalousDimensionClosureStatus) : Prop :=
  s.oneLoopNonLLPoleExcluded ∧
  s.twoLoopNonLLCompositeInsertionComputed ∧
  s.llCompositeInsertionComputed ∧
  s.operatorMixingMatrixDiagonalized

end JanusFormal.P0EFTJanusOneLoopAnomalousDimension
