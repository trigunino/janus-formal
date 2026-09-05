import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

/-! # Global smooth symmetric Einstein tensor in the regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The symmetric part of `G + Λg`, reconstructed as a genuine global smooth
covariant two-tensor from its regular-frame coefficients. -/
def regularGeneralMetricSymmetricEinsteinTensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (regularGeneralMetricSmoothEinsteinCoefficient period hPeriod metric
        cosmologicalConstant first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))

theorem regularGeneralMetricSymmetricEinsteinTensor_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (point : EffectiveQuotient period hPeriod)
    (left right : TangentSpace coverModelWithCorners point) :
    (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        cosmologicalConstant).tensor point left right =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant first second point *
          ((1 / 2 : Real) *
              (regularFrameDualCovector period hPeriod metric first point left *
                regularFrameDualCovector period hPeriod metric second point
                  right) +
            (1 / 2 : Real) *
              (regularFrameDualCovector period hPeriod metric second point left *
                regularFrameDualCovector period hPeriod metric first point
                  right)) := by
  let evaluation :
      SmoothSymmetricCovariantTwoTensor period hPeriod →+ Real :=
    { toFun := fun current => current.tensor point left right
      map_zero' := rfl
      map_add' := by intros; rfl }
  change evaluation (∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (regularGeneralMetricSmoothEinsteinCoefficient period hPeriod metric
        cosmologicalConstant first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  rfl

/-- In the stored frame, the reconstructed tensor is exactly the symmetric
part of the intrinsic Einstein coefficient matrix. -/
@[simp]
theorem regularGeneralMetricSymmetricEinsteinTensor_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (point : EffectiveQuotient period hPeriod)
    (first second : Fin 4) :
    (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        cosmologicalConstant).tensor point (metric.frame first point)
          (metric.frame second point) =
      (1 / 2 : Real) *
        (regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant first second point +
          regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant second first point) := by
  rw [regularGeneralMetricSymmetricEinsteinTensor_apply]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp
  ring

/-- Every canonical chart reads the reconstructed tensor as the symmetric
part of the local intrinsic Einstein bilinear form. -/
theorem regularGeneralMetricSymmetricEinsteinTensor_frame_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        cosmologicalConstant).tensor (patch.coordinateMap coordinate)
          (metric.frame first (patch.coordinateMap coordinate))
          (metric.frame second (patch.coordinateMap coordinate)) =
      (1 / 2 : Real) *
        (localEinsteinBilinearValue period hPeriod metric.metric
            cosmologicalConstant patch coordinate
            (pulledRegularFrameVector period hPeriod metric patch first
              coordinate)
            (pulledRegularFrameVector period hPeriod metric patch second
              coordinate) +
          localEinsteinBilinearValue period hPeriod metric.metric
            cosmologicalConstant patch coordinate
            (pulledRegularFrameVector period hPeriod metric patch second
              coordinate)
            (pulledRegularFrameVector period hPeriod metric patch first
              coordinate)) := by
  rw [regularGeneralMetricSymmetricEinsteinTensor_frame,
    regularGeneralMetricEinsteinCoefficientValue_apply_local,
    regularGeneralMetricEinsteinCoefficientValue_apply_local]

/-- Gate marker: the unrestricted Einstein coefficients now define an
authentic global smooth symmetric metric residual. -/
theorem regular_general_metric_global_smooth_symmetric_einstein_tensor_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : CoordinateVector) (first second : Fin 4),
      (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
          cosmologicalConstant).tensor (patch.coordinateMap coordinate)
            (metric.frame first (patch.coordinateMap coordinate))
            (metric.frame second (patch.coordinateMap coordinate)) =
        (1 / 2 : Real) *
          (localEinsteinBilinearValue period hPeriod metric.metric
              cosmologicalConstant patch coordinate
              (pulledRegularFrameVector period hPeriod metric patch first
                coordinate)
              (pulledRegularFrameVector period hPeriod metric patch second
                coordinate) +
            localEinsteinBilinearValue period hPeriod metric.metric
              cosmologicalConstant patch coordinate
              (pulledRegularFrameVector period hPeriod metric patch second
                coordinate)
              (pulledRegularFrameVector period hPeriod metric patch first
                coordinate)) :=
  regularGeneralMetricSymmetricEinsteinTensor_frame_local period hPeriod metric
    cosmologicalConstant

end
end P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
end JanusFormal
