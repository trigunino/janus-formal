import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D

/-! # Invariant Einstein-tensor variation in the regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricInvariantEinsteinVariation4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The invariant pairing with the global symmetric Einstein tensor is the
regular-coframe coefficient contraction. -/
theorem regularGeneralMetricSymmetricEinsteinTensor_pairing_eq_dualFrameSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
          cosmologicalConstant) variation point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant first second point *
          variation.tensor point
            (regularFrameDualVectorAt period hPeriod metric point first)
            (regularFrameDualVectorAt period hPeriod metric point second) := by
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing :
      SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun tensor =>
        generalMetricTensorPairingAt period hPeriod metric.metric variation
          tensor point
      map_add' := by
        intro first second
        exact generalMetricTensorPairingAt_add_right period hPeriod
          metric.metric variation first second point
      map_smul' := by
        intro scalar tensor
        exact generalMetricTensorPairingAt_smul_right period hPeriod
          metric.metric scalar variation tensor point }
  change pairing
      (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        cosmologicalConstant) = _
  unfold regularGeneralMetricSymmetricEinsteinTensor
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (regularFrameDualCovector period hPeriod metric first)
    (regularFrameDualCovector period hPeriod metric second)
  have hCongr :
      pairing
          (smoothBulkScalarSMulTensor period hPeriod
            (regularGeneralMetricSmoothEinsteinCoefficient period hPeriod
              metric cosmologicalConstant first second) rankOne) =
        pairing
          ((regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant first second point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [hCongr, map_smul]
  apply congrArg
    (regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
      cosmologicalConstant first second point * ·)
  apply generalMetricTensorPairingAt_symmetricMetricRankOne
    (first := regularFrameDualVectorAt period hPeriod metric point first)
    (second := regularFrameDualVectorAt period hPeriod metric point second)
  intro left right
  change
    (1 / 2 : Real) *
          (regularFrameDualCovector period hPeriod metric first point left *
            regularFrameDualCovector period hPeriod metric second point right) +
        (1 / 2 : Real) *
          (regularFrameDualCovector period hPeriod metric second point left *
            regularFrameDualCovector period hPeriod metric first point right) =
      _
  rw [← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing]

/-- Gate marker for the invariant Einstein variation pairing. -/
theorem regular_general_metric_invariant_einstein_variation_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
          cosmologicalConstant) variation point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant first second point *
          variation.tensor point
            (regularFrameDualVectorAt period hPeriod metric point first)
            (regularFrameDualVectorAt period hPeriod metric point second) :=
  regularGeneralMetricSymmetricEinsteinTensor_pairing_eq_dualFrameSum
    period hPeriod metric cosmologicalConstant variation point

end
end P0EFTJanusProgramPRegularGeneralMetricInvariantEinsteinVariation4D
end JanusFormal
