import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonNullGHYMeasureVariation

/-!
Exact inverse-compatible pointwise curve for the non-null GHY density.

For an affine induced-metric curve `h(t) = h + t delta h`, the inverse slot is
the actual matrix inverse `h(t)⁻¹`, not its affine first jet.  Invertibility is
proved on a neighbourhood of the base point, the inverse derivative is derived
from matrix inversion, and the determinant measure is combined with an affine
extrinsic-curvature curve.

This is an algebraic curve of boundary point data.  The extrinsic-curvature
direction is supplied independently; no embedding, Einstein--Hilbert flux or
boundary integration is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusNonNullGHYExactInverseCurve

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation

abbrev Matrix3 := P0EFTJanusExplicitBoundaryDensityLedger.Matrix3

/-- Matrix-valued derivative predicate with the Frobenius instances used by
matrix inversion and multiplication. -/
def FrobeniusMatrixHasDerivAt
    (f : ℝ → Matrix3) (derivative : Matrix3) (point : ℝ) : Prop :=
  @HasFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ
    NormedField.toNormedCommRing.toAddCommGroup
    Semiring.toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Matrix3
    Matrix.frobeniusNormedAddCommGroup.toAddCommGroup
    Matrix.frobeniusNormedSpace.toModule
    Matrix.frobeniusNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f (ContinuousLinearMap.toSpanSingleton ℝ derivative) point

/-- Scalar derivative predicate with the normed real instances produced by
continuous-linear composition from the Frobenius matrix space. -/
def FrobeniusScalarHasDerivAt
    (f : ℝ → ℝ) (derivative point : ℝ) : Prop :=
  @HasFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ
    NormedField.toNormedCommRing.toAddCommGroup
    Semiring.toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ℝ
    Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℝ).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f (ContinuousLinearMap.toSpanSingleton ℝ derivative) point

@[simp]
theorem zeroMeasureExtension_inducedMetricVariation
    (variation : NonNullGHYMetricVariation) :
    (zeroMeasureExtension variation).inducedMetricVariation =
      variation.inducedMetricVariation :=
  rfl

@[simp]
theorem zeroMeasureExtension_extrinsicCurvatureVariation
    (variation : NonNullGHYMetricVariation) :
    (zeroMeasureExtension variation).extrinsicCurvatureVariation =
      variation.extrinsicCurvatureVariation :=
  rfl

/-- Actual Frechet derivative of inversion on `3 x 3` matrices. -/
def matrixInverseDerivative (metric : Matrix3) : Matrix3 →L[ℝ] Matrix3 :=
  -ContinuousLinearMap.mulLeftRight ℝ Matrix3 metric⁻¹ metric⁻¹

@[simp]
theorem matrixInverseDerivative_apply (metric variation : Matrix3) :
    matrixInverseDerivative metric variation =
      -(metric⁻¹ * variation * metric⁻¹) := by
  rfl

/-- Matrix inversion is Frechet differentiable at every invertible `3 x 3`
matrix. -/
theorem matrixInverse_hasFDerivAt
    (metric : Matrix3) (hMetric : IsUnit metric) :
    HasFDerivAt (fun point : Matrix3 => point⁻¹)
      (matrixInverseDerivative metric) metric := by
  obtain ⟨unit, rfl⟩ := hMetric
  convert (hasFDerivAt_ringInverse (𝕜 := ℝ) unit) using 1
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point
    exact Matrix.nonsing_inv_eq_ringInverse point
  · rename_i hAdd hModule hTopology
    cases hAdd
    cases hModule
    cases hTopology
    simp only [matrixInverseDerivative,
      Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
    apply HEq.rfl

/-- The supplied two-sided inverse makes the base induced metric a unit. -/
theorem inducedMetric_isUnit (data : NonNullBoundaryPointData) :
    IsUnit data.inducedMetric := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact Matrix.isUnit_det_of_left_inverse data.inverseWitness.inverse_mul

/-- The supplied inverse agrees with the canonical matrix inverse. -/
theorem inducedMetric_inv_eq_supplied
    (data : NonNullBoundaryPointData) :
    data.inducedMetric⁻¹ = data.inducedInverse :=
  Matrix.inv_eq_left_inv data.inverseWitness.inverse_mul

/-- The actual inverse of the affine induced-metric curve. -/
def exactInducedInverseCurve
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : Matrix3 :=
  (inducedMetricCurve data (zeroMeasureExtension variation) t)⁻¹

@[simp]
theorem exactInducedInverseCurve_zero
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    exactInducedInverseCurve data variation 0 = data.inducedInverse := by
  simp [exactInducedInverseCurve, inducedMetric_inv_eq_supplied]

/-- The affine metric curve stays invertible in a neighbourhood of zero. -/
theorem eventually_inducedMetricCurve_isUnit
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    ∀ᶠ t in nhds (0 : ℝ),
      IsUnit (inducedMetricCurve data (zeroMeasureExtension variation) t) := by
  have hContinuous : ContinuousAt
      (fun t : ℝ =>
        Matrix.det (inducedMetricCurve data
          (zeroMeasureExtension variation) t)) 0 :=
    (inducedMetricDeterminantCurve_hasDerivAt data
      (zeroMeasureExtension variation)).continuousAt
  have hBase :
      Matrix.det (inducedMetricCurve data
        (zeroMeasureExtension variation) 0) ≠ 0 := by
    simpa using inducedMetric_det_ne_zero data
  filter_upwards [hContinuous.eventually_ne hBase] with t hDet
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr hDet

/-- On the local invertibility neighbourhood, the canonical inverse satisfies
both exact inverse identities. -/
theorem exactInducedInverseCurve_inverseWitness_of_isUnit
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ)
    (hUnit :
      IsUnit (inducedMetricCurve data (zeroMeasureExtension variation) t)) :
    Matrix3InverseWitness
      (inducedMetricCurve data (zeroMeasureExtension variation) t)
      (exactInducedInverseCurve data variation t) := by
  have hDet : IsUnit
      (Matrix.det (inducedMetricCurve data
        (zeroMeasureExtension variation) t)) :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hUnit)
  constructor
  · exact Matrix.nonsing_inv_mul _ hDet
  · exact Matrix.mul_nonsing_inv _ hDet

theorem eventually_exactInducedInverseCurve_inverseWitness
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    ∀ᶠ t in nhds (0 : ℝ),
      Matrix3InverseWitness
        (inducedMetricCurve data (zeroMeasureExtension variation) t)
        (exactInducedInverseCurve data variation t) := by
  filter_upwards [eventually_inducedMetricCurve_isUnit data variation]
    with t hUnit
  exact exactInducedInverseCurve_inverseWitness_of_isUnit
    data variation t hUnit

theorem inducedMetricCurve_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusMatrixHasDerivAt
      (inducedMetricCurve data (zeroMeasureExtension variation))
      variation.inducedMetricVariation 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hDerivative :=
    ((hasDerivAt_id (0 : ℝ)).smul_const
      variation.inducedMetricVariation).const_add data.inducedMetric
  exact (hDerivative.congr_deriv
    (one_smul ℝ variation.inducedMetricVariation)).hasFDerivAt

/-- The exact inverse curve has the forced derivative
`-h⁻¹ delta-h h⁻¹`. -/
theorem exactInducedInverseCurve_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusMatrixHasDerivAt (exactInducedInverseCurve data variation)
      (constrainedInverseVariation data (zeroMeasureExtension variation)) 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hComp :=
    (matrixInverse_hasFDerivAt data.inducedMetric
      (inducedMetric_isUnit data)).comp_hasDerivAt_of_eq 0
        (inducedMetricCurve_hasDerivAt data variation) (by
          simp [inducedMetricCurve])
  have hDerivative :
      matrixInverseDerivative data.inducedMetric
          variation.inducedMetricVariation =
        constrainedInverseVariation data
          (zeroMeasureExtension variation) := by
    rw [matrixInverseDerivative_apply, constrainedInverseVariation,
      inducedMetric_inv_eq_supplied]
    rfl
  have hCorrect := hComp.congr_deriv hDerivative
  change HasFDerivAt
    (fun t : ℝ =>
      (inducedMetricCurve data (zeroMeasureExtension variation) t)⁻¹)
    (ContinuousLinearMap.toSpanSingleton ℝ
      (constrainedInverseVariation data (zeroMeasureExtension variation))) 0
  exact hCorrect.hasFDerivAt

/-- Affine extrinsic-curvature curve in the supplied symmetric direction. -/
def exactExtrinsicCurvatureCurve
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : Matrix3 :=
  data.extrinsicCurvature + t • variation.extrinsicCurvatureVariation

theorem exactExtrinsicCurvatureCurve_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusMatrixHasDerivAt (exactExtrinsicCurvatureCurve data variation)
      variation.extrinsicCurvatureVariation 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hDerivative :=
    ((hasDerivAt_id (0 : ℝ)).smul_const
      variation.extrinsicCurvatureVariation).const_add
        data.extrinsicCurvature
  exact (hDerivative.congr_deriv
    (one_smul ℝ variation.extrinsicCurvatureVariation)).hasFDerivAt

/-- Exact inverse/extrinsic trace along the local boundary-data curve. -/
def exactMeanCurvatureTraceCurve
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : ℝ :=
  Matrix.trace
    (exactInducedInverseCurve data variation t *
      exactExtrinsicCurvatureCurve data variation t)

def traceCovector : Matrix3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 3) ℝ ℝ)

@[simp]
theorem traceCovector_apply (matrix : Matrix3) :
    traceCovector matrix = Matrix.trace matrix := by
  rfl

theorem exactMeanCurvatureTraceCurve_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusScalarHasDerivAt (exactMeanCurvatureTraceCurve data variation)
      (meanCurvatureTraceVariation data (zeroMeasureExtension variation)) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hInverse := exactInducedInverseCurve_hasDerivAt data variation
  have hExtrinsic := exactExtrinsicCurvatureCurve_hasDerivAt data variation
  unfold FrobeniusMatrixHasDerivAt at hInverse hExtrinsic
  have hInverseDeriv : HasDerivAt (exactInducedInverseCurve data variation)
      (constrainedInverseVariation data (zeroMeasureExtension variation)) 0 :=
    hInverse.hasDerivAt.congr_deriv (by simp)
  have hExtrinsicDeriv :
      HasDerivAt (exactExtrinsicCurvatureCurve data variation)
        variation.extrinsicCurvatureVariation 0 :=
    hExtrinsic.hasDerivAt.congr_deriv (by simp)
  have hProduct := hInverseDeriv.mul hExtrinsicDeriv
  have hTrace := traceCovector.hasFDerivAt.comp_hasDerivAt 0 hProduct
  have hDerivative :
      traceCovector
          (constrainedInverseVariation data (zeroMeasureExtension variation) *
              exactExtrinsicCurvatureCurve data variation 0 +
            exactInducedInverseCurve data variation 0 *
              variation.extrinsicCurvatureVariation) =
        meanCurvatureTraceVariation data
          (zeroMeasureExtension variation) := by
    simp [traceCovector_apply, meanCurvatureTraceVariation,
      exactExtrinsicCurvatureCurve]
  have hCorrect := hTrace.congr_deriv hDerivative
  change HasFDerivAt
    (fun t : ℝ => Matrix.trace
      (exactInducedInverseCurve data variation t *
        exactExtrinsicCurvatureCurve data variation t))
    (ContinuousLinearMap.toSpanSingleton ℝ
      (meanCurvatureTraceVariation data (zeroMeasureExtension variation))) 0
  exact hCorrect.hasFDerivAt

@[simp]
theorem exactMeanCurvatureTraceCurve_zero
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    exactMeanCurvatureTraceCurve data variation 0 =
      meanCurvatureTrace data := by
  simp [exactMeanCurvatureTraceCurve, exactExtrinsicCurvatureCurve,
    meanCurvatureTrace]

/-- Pointwise GHY density along the exact inverse-compatible metric curve. -/
def nonNullGHYExactInverseCurve
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt
      |Matrix.det
        (inducedMetricCurve data (zeroMeasureExtension variation) t)| *
    exactMeanCurvatureTraceCurve data variation t

@[simp]
theorem nonNullGHYExactInverseCurve_zero
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    nonNullGHYExactInverseCurve einsteinScale data variation 0 =
      nonNullGHYDensity einsteinScale data := by
  simp [nonNullGHYExactInverseCurve, exactMeanCurvatureTraceCurve,
    exactExtrinsicCurvatureCurve, nonNullGHYDensity, meanCurvatureTrace]

/-- Exact pointwise derivative.  The measure tangent is forced by the
determinant and the inverse tangent by actual matrix inversion. -/
theorem nonNullGHYExactInverseCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusScalarHasDerivAt
      (nonNullGHYExactInverseCurve einsteinScale data variation)
      (nonNullGHYFirstVariation einsteinScale data
        (metricFirstJetVariation data variation)) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hMeasure := inducedBoundaryMeasureCurve_hasDerivAt data
    (zeroMeasureExtension variation)
  have hTrace := exactMeanCurvatureTraceCurve_hasDerivAt data variation
  unfold FrobeniusScalarHasDerivAt at hTrace
  have hTraceDeriv : HasDerivAt
      (exactMeanCurvatureTraceCurve data variation)
      (meanCurvatureTraceVariation data (zeroMeasureExtension variation)) 0 :=
    hTrace.hasDerivAt.congr_deriv (by simp)
  have hProduct := (hMeasure.mul hTraceDeriv).const_mul
    (einsteinScale * data.orientationSign)
  have hDerivative :
      einsteinScale * data.orientationSign *
          ((Real.sqrt |Matrix.det data.inducedMetric| / 2 *
                Matrix.trace (data.inducedInverse *
                  variation.inducedMetricVariation)) *
              meanCurvatureTrace data +
            Real.sqrt |Matrix.det data.inducedMetric| *
              meanCurvatureTraceVariation data
                (zeroMeasureExtension variation)) =
        nonNullGHYFirstVariation einsteinScale data
          (metricFirstJetVariation data variation) := by
    simp [metricFirstJetVariation, nonNullGHYFirstVariation,
      metricMeasureVariation]
  have hCorrect := hProduct.congr_deriv (by
    simpa using hDerivative)
  exact (hCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp [nonNullGHYExactInverseCurve]
      ring)).hasFDerivAt

end

end P0EFTJanusNonNullGHYExactInverseCurve
end JanusFormal
