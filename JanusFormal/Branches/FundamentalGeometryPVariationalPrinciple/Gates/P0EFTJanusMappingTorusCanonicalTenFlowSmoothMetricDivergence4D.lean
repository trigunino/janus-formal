import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceMetricIndependence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-!
# Canonical ten-flow divergence with an arbitrary smooth metric dualizer

The redundant ten-flow coefficients only need a smooth Lorentz metric.  This
file removes the unnecessary regular-frame wrapper, proves weak Stokes for the
general construction, and identifies every such construction with the
canonical divergence already used by the physical metric sector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowSmoothMetricDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

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

/-- Redundant smooth coefficient obtained from any smooth Lorentz dualizer. -/
def canonicalTenFlowSmoothMetricDualCoefficient
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Fin 10) : SmoothQuotientField period hPeriod Real :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (canonicalTenFlowFrame period hPeriod) dualMetric vector index

@[simp]
theorem canonicalTenFlowSmoothMetricDualCoefficient_apply
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Fin 10) (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric vector
        index point =
      generalMetricFiniteFrameCoefficientAt period hPeriod
        (canonicalTenFlowFrame period hPeriod) dualMetric point index
          (vector point) :=
  rfl

/-- The coefficients reconstruct the current for every smooth dualizer. -/
theorem canonicalTenFlowSmoothMetricDual_reconstructs
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    vector point =
      ∑ index : Fin 10,
        canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
            vector index point •
          canonicalTenFlowGeneratorAt period hPeriod point
            ((canonicalFlowIndexEquivFinTen).symm index) := by
  exact generalMetricFiniteFrame_reconstructs period hPeriod
    (canonicalTenFlowFrame period hPeriod) dualMetric vector point

/-- Ten-flow divergence presented with an arbitrary smooth Lorentz dualizer. -/
def canonicalTenFlowSmoothMetricDivergence
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    ∑ index : Fin 10,
      frameDerivative period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
          vector index) point index
  contMDiff_toFun := by
    apply ContMDiff.sum
    intro index _
    exact (contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
          vector index))) index

@[simp]
theorem canonicalTenFlowSmoothMetricDivergence_apply
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowSmoothMetricDivergence period hPeriod dualMetric vector point =
      ∑ index : Fin 10,
        frameDerivative period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
            vector index) point index :=
  rfl

/-- Reconstruction commutes with the differential of every smooth test. -/
theorem canonicalTenFlowSmoothMetricDirectionalDerivative_reconstructs
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    mvfderiv coverModelWithCorners test.toFun point (vector point) =
      ∑ index : Fin 10,
        canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
            vector index point *
          frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) test point index := by
  rw [canonicalTenFlowSmoothMetricDual_reconstructs period hPeriod dualMetric
    vector point]
  simp only [map_sum, map_smul, smul_eq_mul, frameDerivative_eq_mfderiv]
  apply Finset.sum_congr rfl
  intro index _
  rfl

private theorem leftSummand_integrable
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) (index : Fin 10) :
    Integrable
      (fun point => test point *
        frameDerivative period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
            vector index) point index)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact (test.contMDiff_toFun.continuous.mul
    ((contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
          vector index))) index).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

private theorem rightSummand_integrable
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) (index : Fin 10) :
    Integrable
      (fun point =>
        frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) test point index *
          canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric
            vector index point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact (((contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod) test)) index).continuous.mul
    (canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric vector
      index).contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Weak Stokes depends only on reconstruction and the volume-preserving
canonical flows, hence holds for every smooth metric dualizer. -/
theorem canonicalTenFlowSmoothMetricDivergence_weak_stokes
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) :
    (∫ point,
        test point *
          canonicalTenFlowSmoothMetricDivergence period hPeriod dualMetric
            vector point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      -∫ point,
        mvfderiv coverModelWithCorners test.toFun point (vector point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let coefficient :=
    canonicalTenFlowSmoothMetricDualCoefficient period hPeriod dualMetric vector
  let derivative := fun (field : SmoothQuotientField period hPeriod Real)
      (point : EffectiveQuotient period hPeriod) (index : Fin 10) =>
    frameDerivative period hPeriod Real
      (canonicalTenFlowFrame period hPeriod) field point index
  have hIPP (index : Fin 10) :
      (∫ point, test point * derivative (coefficient index) point index ∂measure) =
        -∫ point, derivative test point index * coefficient index point
          ∂measure := by
    simpa only [measure, coefficient, derivative, RCLike.inner_apply,
      conj_trivial, mul_comm] using
      canonicalTenFlowFrame_integral_inner_derivative_eq_neg period hPeriod
        index test (coefficient index)
  calc
    (∫ point,
        test point *
          canonicalTenFlowSmoothMetricDivergence period hPeriod dualMetric
            vector point ∂measure) =
        ∑ index : Fin 10,
          ∫ point, test point * derivative (coefficient index) point index
            ∂measure := by
      rw [← integral_finsetSum Finset.univ (fun index _ =>
        leftSummand_integrable period hPeriod dualMetric vector test index)]
      apply integral_congr_ae
      filter_upwards [] with point
      simp only [canonicalTenFlowSmoothMetricDivergence_apply,
        Finset.mul_sum]
    _ = ∑ index : Fin 10,
        -∫ point, derivative test point index * coefficient index point
          ∂measure := by
      apply Finset.sum_congr rfl
      intro index _
      exact hIPP index
    _ = -∫ point,
        ∑ index : Fin 10,
          derivative test point index * coefficient index point ∂measure := by
      rw [Finset.sum_neg_distrib,
        integral_finsetSum Finset.univ (fun index _ =>
          rightSummand_integrable period hPeriod dualMetric vector test index)]
    _ = -∫ point,
        mvfderiv coverModelWithCorners test.toFun point (vector point)
          ∂measure := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with point
      rw [canonicalTenFlowSmoothMetricDirectionalDerivative_reconstructs
        period hPeriod dualMetric vector test point]
      apply Finset.sum_congr rfl
      intro index _
      ring

private theorem smoothScalar_eq_of_equal_weak_pairings
    (first second : SmoothQuotientField period hPeriod Real)
    (hPairing : ∀ test : SmoothQuotientField period hPeriod Real,
      (∫ point, test point * first point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, test point * second point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) :
    first = second := by
  let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let residual := first - second
  have hFirstIntegrable : Integrable
      (fun point => residual point * first point) measure :=
    (residual.contMDiff_toFun.continuous.mul first.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSecondIntegrable : Integrable
      (fun point => residual point * second point) measure :=
    (residual.contMDiff_toFun.continuous.mul second.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSquareIntegral :
      (∫ point, residual point * residual point ∂measure) = 0 := by
    calc
      _ = (∫ point, residual point * first point ∂measure) -
          ∫ point, residual point * second point ∂measure := by
        rw [← integral_sub hFirstIntegrable hSecondIntegrable]
        apply integral_congr_ae
        filter_upwards [] with point
        change
          (first point - second point) * (first point - second point) =
            (first point - second point) * first point -
              (first point - second point) * second point
        ring
      _ = 0 := by
        rw [hPairing residual]
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
  change first point - second point = 0 at hPoint
  exact sub_eq_zero.mp hPoint

/-- Any smooth dualizer presentation equals the existing regular-metric
presentation of the canonical divergence. -/
theorem canonicalTenFlowSmoothMetricDivergence_eq_regular
    (dualMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    canonicalTenFlowSmoothMetricDivergence period hPeriod dualMetric vector =
      canonicalTenFlowDivergence period hPeriod metric vector := by
  apply smoothScalar_eq_of_equal_weak_pairings period hPeriod
  intro test
  rw [canonicalTenFlowSmoothMetricDivergence_weak_stokes period hPeriod,
    canonicalTenFlowDivergence_weak_stokes period hPeriod]

/-- Canonical divergence presented with the intrinsic quotient metric. -/
def canonicalIntrinsicTenFlowDivergence
    (vector : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real :=
  canonicalTenFlowSmoothMetricDivergence period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) vector

/-- The intrinsic-metric presentation equals every regular presentation. -/
theorem canonicalIntrinsicTenFlowDivergence_eq_regular
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    canonicalIntrinsicTenFlowDivergence period hPeriod vector =
      canonicalTenFlowDivergence period hPeriod metric vector :=
  canonicalTenFlowSmoothMetricDivergence_eq_regular period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) metric vector

/-- Gate marker: the canonical divergence has an intrinsic smooth-metric
presentation and agrees pointwise with the physical regular presentation. -/
theorem canonical_ten_flow_smooth_metric_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    canonicalIntrinsicTenFlowDivergence period hPeriod vector =
        canonicalTenFlowDivergence period hPeriod metric vector ∧
      ∀ test : SmoothQuotientField period hPeriod Real,
        (∫ point,
            test point * canonicalIntrinsicTenFlowDivergence period hPeriod
              vector point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
          -∫ point,
            mvfderiv coverModelWithCorners test.toFun point (vector point)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  refine ⟨canonicalIntrinsicTenFlowDivergence_eq_regular period hPeriod metric
      vector, ?_⟩
  exact canonicalTenFlowSmoothMetricDivergence_weak_stokes period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) vector

end
end P0EFTJanusMappingTorusCanonicalTenFlowSmoothMetricDivergence4D
end JanusFormal
