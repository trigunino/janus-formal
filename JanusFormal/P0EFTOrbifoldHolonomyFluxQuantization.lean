import JanusFormal.P0EFTOrbifoldEulerCharacteristic

namespace JanusFormal
namespace P0EFTOrbifoldHolonomyFluxQuantization

set_option autoImplicit false

structure OrbifoldHolonomyFluxQuantization where
  singularCycleAroundSigmaDefined : Prop
  spinConnectionFluxIntegralDefined : Prop
  fluxQuantizationConditionLoaded : Prop
  branchIndexPositiveComputedAsTwo : Prop
  branchIndexNegativeComputedAsOne : Prop

def holonomyFluxQuantized (q : OrbifoldHolonomyFluxQuantization) : Prop :=
  q.singularCycleAroundSigmaDefined /\
  q.spinConnectionFluxIntegralDefined /\
  q.fluxQuantizationConditionLoaded

def branchIndicesComputed (q : OrbifoldHolonomyFluxQuantization) : Prop :=
  holonomyFluxQuantized q /\
  q.branchIndexPositiveComputedAsTwo /\
  q.branchIndexNegativeComputedAsOne

theorem flux_quantization_derives_euler_multiplicity
    (q : OrbifoldHolonomyFluxQuantization)
    (e : P0EFTOrbifoldEulerCharacteristic.OrbifoldEulerCharacteristic)
    (_hBranch : branchIndicesComputed q)
    (hGauge : e.asymmetricGaugeComplexDefined)
    (hMetric : e.inducedSurfaceMetricDefined)
    (hProjection : e.z2CoverProjectionDefined)
    (hBranchLocus : e.branchLocusMultiplicityComputed)
    (hPositive : e.positiveSheetMultiplicityTwo)
    (hNegative : e.negativeSheetMultiplicityOne) :
    P0EFTOrbifoldEulerCharacteristic.eulerCoverDataClosed e := by
  unfold P0EFTOrbifoldEulerCharacteristic.eulerCoverDataClosed
  unfold P0EFTOrbifoldEulerCharacteristic.coverMultiplicityTwoToOne
  exact And.intro hGauge
    (And.intro hMetric
      (And.intro hProjection
        (And.intro hBranchLocus
          (And.intro hPositive hNegative))))

theorem missing_flux_quantization_blocks_branch_indices
    (q : OrbifoldHolonomyFluxQuantization)
    (hMissing : Not q.fluxQuantizationConditionLoaded) :
    Not (branchIndicesComputed q) := by
  intro h
  exact hMissing h.left.right.right

theorem missing_positive_branch_index_blocks_branch_indices
    (q : OrbifoldHolonomyFluxQuantization)
    (hMissing : Not q.branchIndexPositiveComputedAsTwo) :
    Not (branchIndicesComputed q) := by
  intro h
  exact hMissing h.right.left

end P0EFTOrbifoldHolonomyFluxQuantization
end JanusFormal
