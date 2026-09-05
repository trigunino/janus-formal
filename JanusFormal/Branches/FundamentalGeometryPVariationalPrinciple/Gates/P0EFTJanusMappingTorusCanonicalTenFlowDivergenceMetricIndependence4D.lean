import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

/-!
# Metric independence of the canonical ten-flow divergence

The metric in the redundant dual coefficients is only a reconstruction aid.
Weak Stokes and full support prove that the resulting smooth divergence is
independent of that choice.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowDivergenceMetricIndependence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance intrinsicCanonicalLorentzVolumeMeasureIsOpenPos :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Two redundant metric dualizers give the same canonical divergence. -/
theorem canonicalTenFlowDivergence_metric_independent
    (first second : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    canonicalTenFlowDivergence period hPeriod first vector =
      canonicalTenFlowDivergence period hPeriod second vector := by
  let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let firstDivergence :=
    canonicalTenFlowDivergence period hPeriod first vector
  let secondDivergence :=
    canonicalTenFlowDivergence period hPeriod second vector
  let residual := firstDivergence - secondDivergence
  have hFirstIntegrable : Integrable
      (fun point => residual point * firstDivergence point) measure :=
    (residual.contMDiff_toFun.continuous.mul
      firstDivergence.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSecondIntegrable : Integrable
      (fun point => residual point * secondDivergence point) measure :=
    (residual.contMDiff_toFun.continuous.mul
      secondDivergence.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFirst := canonicalTenFlowDivergence_weak_stokes period hPeriod first
    vector residual
  have hSecond := canonicalTenFlowDivergence_weak_stokes period hPeriod second
    vector residual
  have hSquareIntegral :
      (∫ point, residual point * residual point ∂measure) = 0 := by
    calc
      _ = ∫ point,
          residual point * firstDivergence point -
            residual point * secondDivergence point ∂measure := by
        apply integral_congr_ae
        filter_upwards [] with point
        change
          (firstDivergence point - secondDivergence point) *
              (firstDivergence point - secondDivergence point) =
            (firstDivergence point - secondDivergence point) *
                firstDivergence point -
              (firstDivergence point - secondDivergence point) *
                secondDivergence point
        ring
      _ = (∫ point, residual point * firstDivergence point ∂measure) -
          ∫ point, residual point * secondDivergence point ∂measure := by
        rw [integral_sub hFirstIntegrable hSecondIntegrable]
      _ = 0 := by
        rw [hFirst, hSecond]
        ring
  have hSquareIntegrable :
      Integrable (fun point => residual point * residual point) measure :=
    (residual.contMDiff_toFun.continuous.mul
      residual.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSquareZero :
      (fun point => residual point * residual point) =ᵐ[measure] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun point => mul_self_nonneg (residual point)) hSquareIntegrable).mp
        hSquareIntegral
  have hResidualZero : residual.toFun =ᵐ[measure]
      (fun _ : EffectiveQuotient period hPeriod => (0 : Real)) := by
    filter_upwards [hSquareZero] with point hPoint
    exact mul_self_eq_zero.mp hPoint
  have hResidualFunctionZero : residual.toFun =
      (fun _ : EffectiveQuotient period hPeriod => (0 : Real)) :=
    (Continuous.ae_eq_iff_eq measure residual.contMDiff_toFun.continuous
      continuous_const).mp hResidualZero
  ext point
  have hPoint := congrFun hResidualFunctionZero point
  change firstDivergence point - secondDivergence point = 0 at hPoint
  exact sub_eq_zero.mp hPoint

/-- Gate marker: the canonical weak divergence is intrinsic to the current and
the canonical volume, despite its redundant metric-dependent presentation. -/
theorem canonical_ten_flow_divergence_metric_independence_gate
    (first second : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    canonicalTenFlowDivergence period hPeriod first vector =
      canonicalTenFlowDivergence period hPeriod second vector :=
  canonicalTenFlowDivergence_metric_independent period hPeriod first second vector

end
end P0EFTJanusMappingTorusCanonicalTenFlowDivergenceMetricIndependence4D
end JanusFormal
