import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D

/-!
# Levi--Civita trace in the regular frame

Metric compatibility and torsion freedom reduce `Γᵃ_ab` to the logarithmic
metric-volume derivative plus the trace of the frame anholonomy.  This is the
finite-dimensional algebraic half of the Palatini/canonical-divergence bridge.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D
open P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Matrix4 := Matrix Index4 Index4 Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Half of the inverse-metric contraction of the regular-frame metric
derivative. -/
def regularFrameMetricHalfTraceDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    ∑ first : Index4, ∑ second : Index4,
      smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric first second)
        (frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameMetricMatrix period hPeriod metric first second) vector)

/-- Trace `Cᵃ_ab` of the regular-frame anholonomy. -/
def regularFrameAnholonomyTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) : SmoothScalarField period hPeriod :=
  ∑ derivative : Index4,
    regularFrameStructureCoefficient period hPeriod metric derivative vector
      derivative

/-- Metric compatibility contracts to the trace `Γᵃ_ba`. -/
private theorem regularFrameMetricHalfTraceDerivative_eq_connectionTrace_swapped
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) (point : EffectiveQuotient period hPeriod) :
    regularFrameMetricHalfTraceDerivative period hPeriod metric vector point =
      ∑ derivative : Index4,
        regularGeneralMetricC0Christoffel period hPeriod metric 0 derivative
          vector derivative point := by
  let matrix : Matrix4 :=
    regularFrameMetricMatrixMap period hPeriod metric point
  let inverse : Matrix4 :=
    regularFrameMetricInverseMatrixMap period hPeriod metric point
  let connection : Index4 → Index4 → Index4 → Real :=
    fun upper first second =>
      regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
        second point
  let metricDerivative : Index4 → Index4 → Real :=
    fun first second =>
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        vector first second point
  have hMetricSymmetric (first second : Index4) :
      matrix first second = matrix second first := by
    change
      metric.metric.tensor.tensor point (metric.frame first point)
          (metric.frame second point) =
        metric.metric.tensor.tensor point (metric.frame second point)
          (metric.frame first point)
    exact metric.metric.tensor.symmetric point _ _
  have hInverseMul : inverse * matrix = 1 := by
    exact Matrix.nonsing_inv_mul matrix
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hMulInverse : matrix * inverse = 1 := by
    exact Matrix.mul_nonsing_inv matrix
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hFirstContraction (first upper : Index4) :
      (∑ second : Index4,
          inverse first second * matrix upper second) =
        (1 : Matrix4) first upper := by
    have hEntry := congrFun (congrFun hInverseMul first) upper
    change (∑ second : Index4,
      inverse first second * matrix second upper) =
        (1 : Matrix4) first upper at hEntry
    calc
      (∑ second : Index4,
          inverse first second * matrix upper second) =
          ∑ second : Index4,
            inverse first second * matrix second upper := by
        apply Finset.sum_congr rfl
        intro second _
        rw [hMetricSymmetric upper second]
      _ = _ := hEntry
  have hSecondContraction (second upper : Index4) :
      (∑ first : Index4,
          inverse first second * matrix first upper) =
        (1 : Matrix4) upper second := by
    have hEntry := congrFun (congrFun hMulInverse upper) second
    change (∑ first : Index4,
      matrix upper first * inverse first second) =
        (1 : Matrix4) upper second at hEntry
    calc
      (∑ first : Index4,
          inverse first second * matrix first upper) =
          ∑ first : Index4,
            matrix upper first * inverse first second := by
        apply Finset.sum_congr rfl
        intro first _
        rw [hMetricSymmetric first upper]
        ring
      _ = _ := hEntry
  have hCompatible (first second : Index4) :
      metricDerivative first second =
        (∑ upper : Index4,
          connection upper vector first * matrix upper second) +
        ∑ upper : Index4,
          connection upper vector second * matrix first upper := by
    exact regularGeneralMetricC0MetricFirstDerivative_zero_metricCompatible
      period hPeriod metric point vector first second
  have hFirst :
      (∑ first : Index4, ∑ second : Index4,
          inverse first second *
            (∑ upper : Index4,
              connection upper vector first * matrix upper second)) =
        ∑ derivative : Index4, connection derivative vector derivative := by
    simp_rw [Finset.mul_sum]
    calc
      (∑ first : Index4, ∑ second : Index4, ∑ upper : Index4,
          inverse first second *
            (connection upper vector first * matrix upper second)) =
          ∑ first : Index4, ∑ upper : Index4, ∑ second : Index4,
            inverse first second *
              (connection upper vector first * matrix upper second) := by
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.sum_comm]
      _ = ∑ first : Index4, ∑ upper : Index4,
          connection upper vector first * (1 : Matrix4) first upper := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro upper _
        rw [← hFirstContraction first upper]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro second _
        ring
      _ = ∑ derivative : Index4,
          connection derivative vector derivative := by
        simp [Matrix.one_apply]
  have hSecond :
      (∑ first : Index4, ∑ second : Index4,
          inverse first second *
            (∑ upper : Index4,
              connection upper vector second * matrix first upper)) =
        ∑ derivative : Index4, connection derivative vector derivative := by
    simp_rw [Finset.mul_sum]
    calc
      (∑ first : Index4, ∑ second : Index4, ∑ upper : Index4,
          inverse first second *
            (connection upper vector second * matrix first upper)) =
          ∑ second : Index4, ∑ upper : Index4, ∑ first : Index4,
            inverse first second *
              (connection upper vector second * matrix first upper) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro second _
        rw [Finset.sum_comm]
      _ = ∑ second : Index4, ∑ upper : Index4,
          connection upper vector second * (1 : Matrix4) upper second := by
        apply Finset.sum_congr rfl
        intro second _
        apply Finset.sum_congr rfl
        intro upper _
        rw [← hSecondContraction second upper]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro first _
        ring
      _ = ∑ derivative : Index4,
          connection derivative vector derivative := by
        simp [Matrix.one_apply]
  have hDerivativeValue (first second : Index4) :
      frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameMetricMatrix period hPeriod metric first second) point
          vector = metricDerivative first second := by
    have hField := congrArg
      (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
      (regularGeneralMetricC0MetricFirstDerivative_zero period hPeriod metric
        vector first second)
    exact hField.symm
  change
    (1 / 2 : Real) *
        (∑ first : Index4, ∑ second : Index4,
          inverse first second *
            frameDerivative period hPeriod Real
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              (regularFrameMetricMatrix period hPeriod metric first second)
              point vector) =
      ∑ derivative : Index4, connection derivative vector derivative
  simp_rw [hDerivativeValue]
  simp_rw [hCompatible]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hFirst, hSecond]
  ring

/-- Torsion freedom converts `Γᵃ_ba` to `Γᵃ_ab` and contributes exactly the
anholonomy trace. -/
theorem regularFrameLeviCivitaTrace_eq_halfTrace_add_anholonomy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) :
    regularFrameLeviCivitaTrace period hPeriod metric vector =
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector +
        regularFrameAnholonomyTrace period hPeriod metric vector := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hSmoothChristoffel (upper first second : Index4) :
      regularFrameSmoothChristoffelCoefficient period hPeriod metric upper first
          second point =
        regularGeneralMetricC0Christoffel period hPeriod metric 0 upper first
          second point := by
    have hField := congrArg
      (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
      (regularGeneralMetricC0Christoffel_zero_smooth period hPeriod metric upper
        first second)
    exact hField.symm
  have hTorsion (derivative : Index4) :
      regularGeneralMetricC0Christoffel period hPeriod metric 0 derivative
            derivative vector point =
        regularGeneralMetricC0Christoffel period hPeriod metric 0 derivative
            vector derivative point +
          regularFrameStructureCoefficient period hPeriod metric derivative
            vector derivative point := by
    have h := regularGeneralMetricC0Christoffel_zero_torsionFree period hPeriod
      metric point derivative derivative vector
    change _ - _ =
      regularFrameStructureCoefficient period hPeriod metric derivative vector
        derivative point at h
    linarith
  unfold regularFrameLeviCivitaTrace regularFrameAnholonomyTrace
  change
    (∑ derivative : Index4,
      regularFrameSmoothChristoffelCoefficient period hPeriod metric derivative
        derivative vector point) =
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector point +
        ∑ derivative : Index4,
          regularFrameStructureCoefficient period hPeriod metric derivative
            vector derivative point
  simp_rw [hSmoothChristoffel]
  simp_rw [hTorsion]
  rw [Finset.sum_add_distrib]
  rw [regularFrameMetricHalfTraceDerivative_eq_connectionTrace_swapped
    period hPeriod metric vector point]

/-- Gate marker: the connection trace is reduced to metric-volume derivative
and frame anholonomy with no unproved geometric contract. -/
theorem regular_frame_levi_civita_trace_reduction_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) :
    regularFrameLeviCivitaTrace period hPeriod metric vector =
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector +
        regularFrameAnholonomyTrace period hPeriod metric vector :=
  regularFrameLeviCivitaTrace_eq_halfTrace_add_anholonomy period hPeriod metric
    vector

end
end P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D
end JanusFormal
