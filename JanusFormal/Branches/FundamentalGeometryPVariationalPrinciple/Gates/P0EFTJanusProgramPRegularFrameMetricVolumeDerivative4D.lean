import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D

/-!
# Directional derivative of regular-frame metric volume

The stored regular metric volume is the square root of the absolute determinant
of the genuine frame Gram matrix.  Differentiating this identity along each
frame vector gives the exact half inverse-metric trace formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMetricVolumeDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix Matrix.Norms.Frobenius
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Matrix4 := Matrix Index4 Index4 Real

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def matrixEntryCLM (row column : Index4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The directional derivative of the stored metric volume is the stored
volume times one half of the inverse-metric contraction of the frame metric
derivative. -/
theorem regularFrameMetricVolume_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (vector : Index4) :
    frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.volume point vector =
      metric.volume point *
        regularFrameMetricHalfTraceDerivative period hPeriod metric vector
          point := by
  classical
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let matrixMap := regularFrameMetricMatrixMap period hPeriod metric
  let matrix : Matrix4 := matrixMap point
  let direction : Matrix4 := fun first second =>
    frameDerivative period hPeriod Real frame
      (regularFrameMetricMatrix period hPeriod metric first second) point vector
  have hMetricFieldSymmetric (first second : Index4) :
      regularFrameMetricMatrix period hPeriod metric first second =
        regularFrameMetricMatrix period hPeriod metric second first := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro current
    exact metric.metric.tensor.symmetric current
      (metric.frame first current) (metric.frame second current)
  have hDirectionSymmetric (first second : Index4) :
      direction first second = direction second first := by
    change frameDerivative period hPeriod Real frame
        (regularFrameMetricMatrix period hPeriod metric first second) point
          vector =
      frameDerivative period hPeriod Real frame
        (regularFrameMetricMatrix period hPeriod metric second first) point
          vector
    rw [hMetricFieldSymmetric first second]
  have hMatrixMDiff : MDifferentiableAt coverModelWithCorners
      (modelWithCornersSelf Real Matrix4) matrixMap point :=
    (regularFrameMetricMatrixMap_contMDiff period hPeriod metric)
      |>.mdifferentiableAt (by simp)
  have hEntryDerivative (first second : Index4) :
      frameDerivative period hPeriod Real frame
          (regularFrameMetricMatrix period hPeriod metric first second) point
          vector =
        (mfderiv coverModelWithCorners (modelWithCornersSelf Real Matrix4)
          matrixMap point (metric.frame vector point)) first second := by
    let entry := matrixEntryCLM first second
    have hEntry : MDifferentiableAt (modelWithCornersSelf Real Matrix4)
        𝓘(Real, Real) entry (matrixMap point) :=
      entry.differentiableAt.mdifferentiableAt
    have hChain := mfderiv_comp_apply point hEntry hMatrixMDiff
      (metric.frame vector point)
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
    change
      (mfderiv coverModelWithCorners 𝓘(Real, Real)
          (entry ∘ matrixMap) point (metric.frame vector point) : Real) =
        entry (mfderiv coverModelWithCorners
          (modelWithCornersSelf Real Matrix4) matrixMap point
          (metric.frame vector point)) at hChain
    rw [frameDerivative_eq_mfderiv]
    unfold mvfderiv
    change
      (mfderiv coverModelWithCorners 𝓘(Real, Real)
          (regularFrameMetricMatrix period hPeriod metric first second).toFun
          point (metric.frame vector point) : Real) =
        (mfderiv coverModelWithCorners
          (modelWithCornersSelf Real Matrix4) matrixMap point
          (metric.frame vector point)) first second
    convert hChain using 1 <;>
      rfl
  have hMatrixDerivative :
      mfderiv coverModelWithCorners (modelWithCornersSelf Real Matrix4)
          matrixMap point (metric.frame vector point) = direction := by
    apply (NormedSpace.fromTangentSpace (matrixMap point)).injective
    change (NormedSpace.fromTangentSpace (matrixMap point))
        (mfderiv coverModelWithCorners (modelWithCornersSelf Real Matrix4)
          matrixMap point (metric.frame vector point)) = direction
    ext first second
    exact (hEntryDerivative first second).symm
  have hDet : Matrix.det matrix ≠ 0 := by
    exact regularFrameMetricMatrix_det_ne_zero period hPeriod metric point
  let base : FixedSignMetric4 :=
    { metric := matrix
      orientation := Matrix.det matrix
      orientation_ne_zero := hDet
      metric_symmetric := by
        ext first second
        change matrix second first = matrix first second
        exact (metric.metric.tensor.symmetric point
          (metric.frame second point) (metric.frame first point))
      metric_mem_domain := by
        change 0 < Matrix.det matrix * Matrix.det matrix
        exact mul_self_pos.mpr hDet }
  let variation : SymmetricMetricVariation4 :=
    { tensor := direction
      tensor_symmetric := by
        ext first second
        exact hDirectionSymmetric second first }
  let volumeOnMatrices : Matrix4 → Real := fun current =>
    Real.sqrt |Matrix.det current|
  have hMatrixVolume : DifferentiableAt Real volumeOnMatrices matrix := by
    have hDetDerivative := determinant_hasFDerivAt matrix
    unfold FrobeniusHasFDerivAt at hDetDerivative
    exact ((hDetDerivative.abs hDet).sqrt (abs_ne_zero.mpr hDet))
      |>.differentiableAt
  have hCurve := metricCurve_hasDerivAt base variation
  unfold FrobeniusMatrixHasDerivAt at hCurve
  have hCurveDerivative : HasDerivAt (metricCurve base variation)
      variation.tensor 0 :=
    hCurve.hasDerivAt.congr_deriv (by simp)
  have hComposed : HasDerivAt
      (fun t : Real => volumeOnMatrices (metricCurve base variation t))
      ((fderiv Real volumeOnMatrices matrix) direction) 0 := by
    exact hMatrixVolume.hasFDerivAt.comp_hasDerivAt_of_eq 0
      hCurveDerivative (by simp [base, variation])
  have hDirectional :
      (fderiv Real volumeOnMatrices matrix) direction =
        (Real.sqrt |Matrix.det matrix| / 2) *
          Matrix.trace (matrix⁻¹ * direction) := by
    simpa [base, variation, relativeMetricVariation] using
      hComposed.unique (metricMeasureCurve_hasDerivAt base variation)
  have hVolumeFunction :
      metric.volume.toFun = volumeOnMatrices ∘ matrixMap := by
    funext current
    rw [metric.volume_eq current]
    rfl
  have hVolumeMDiff : MDifferentiableAt
      (modelWithCornersSelf Real Matrix4) 𝓘(Real, Real)
      volumeOnMatrices matrix :=
    hMatrixVolume.mdifferentiableAt
  have hChain := mfderiv_comp_apply point hVolumeMDiff hMatrixMDiff
    (metric.frame vector point)
  rw [mfderiv_eq_fderiv, hMatrixDerivative] at hChain
  change _ = (fderiv Real volumeOnMatrices matrix) direction at hChain
  rw [hDirectional] at hChain
  change
    (mfderiv coverModelWithCorners 𝓘(Real, Real)
        (volumeOnMatrices ∘ matrixMap) point (metric.frame vector point) : Real) =
      (Real.sqrt |Matrix.det matrix| / 2) *
        Matrix.trace (matrix⁻¹ * direction) at hChain
  have hVolumeDerivative :
      frameDerivative period hPeriod Real frame metric.volume point vector =
        (Real.sqrt |Matrix.det matrix| / 2) *
          Matrix.trace (matrix⁻¹ * direction) := by
    rw [frameDerivative_eq_mfderiv]
    unfold mvfderiv
    rw [hVolumeFunction]
    change
      (mfderiv coverModelWithCorners 𝓘(Real, Real)
          (volumeOnMatrices ∘ matrixMap) point
          (metric.frame vector point) : Real) = _
    exact hChain
  rw [hVolumeDerivative, metric.volume_eq point]
  change
    (Real.sqrt |Matrix.det matrix| / 2) *
        Matrix.trace (matrix⁻¹ * direction) =
      Real.sqrt |Matrix.det matrix| *
        ((1 / 2 : Real) *
          ∑ first : Index4, ∑ second : Index4,
            matrix⁻¹ first second * direction first second)
  have hTrace : Matrix.trace (matrix⁻¹ * direction) =
      ∑ first : Index4, ∑ second : Index4,
        matrix⁻¹ first second * direction first second := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [hDirectionSymmetric second first]
  rw [hTrace]
  ring

/-- Gate marker for the exact regular-frame derivative of metric volume. -/
theorem regular_frame_metric_volume_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ∀ (point : EffectiveQuotient period hPeriod) (vector : Index4),
      frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.volume point vector =
        metric.volume point *
          regularFrameMetricHalfTraceDerivative period hPeriod metric vector
            point :=
  regularFrameMetricVolume_frameDerivative period hPeriod metric

end
end P0EFTJanusProgramPRegularFrameMetricVolumeDerivative4D
end JanusFormal
