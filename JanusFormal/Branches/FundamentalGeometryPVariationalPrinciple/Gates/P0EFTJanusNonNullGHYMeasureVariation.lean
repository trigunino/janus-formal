import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonNullGHYFirstVariation

/-!
Metric-induced first variation of the non-null boundary measure.

For an invertible symmetric induced metric `h` and a symmetric variation
`delta h`, this gate derives the Jacobi formula along `h + t delta h`, passes
through absolute value and square root, and substitutes the resulting measure
tangent into the pointwise GHY first variation.

The inverse-metric slot uses its forced affine first jet
`h⁻¹ - t h⁻¹ (delta h) h⁻¹`.  This has the correct derivative at the base
point, but is not asserted to equal `(h + t delta h)⁻¹` away from that point.
Accordingly the public curve and theorem below are explicitly named as
first-jet results, not as an exact curve of inverse-compatible boundary data.

This remains a pointwise first-order statement.  It neither integrates a
boundary face nor proves cancellation with the Einstein--Hilbert bulk flux.
-/

namespace JanusFormal
namespace P0EFTJanusNonNullGHYMeasureVariation

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations
open P0EFTJanusNonNullGHYFirstVariation

abbrev Matrix3 := P0EFTJanusExplicitBoundaryDensityLedger.Matrix3

/-- Independent metric/extrinsic boundary variation data.  Unlike the record
from the preceding gate, it has no independently supplied measure tangent. -/
structure NonNullGHYMetricVariation where
  inducedMetricVariation : Matrix3
  extrinsicCurvatureVariation : Matrix3
  inducedMetricVariationSymmetric :
    inducedMetricVariation.transpose = inducedMetricVariation
  extrinsicCurvatureVariationSymmetric :
    extrinsicCurvatureVariation.transpose = extrinsicCurvatureVariation

/-- Internal adapter to the preceding first-variation gate.  Its zero measure
slot is always overwritten by the determinant-derived value below. -/
def zeroMeasureExtension
    (variation : NonNullGHYMetricVariation) : NonNullGHYVariation where
  inducedMetricVariation := variation.inducedMetricVariation
  extrinsicCurvatureVariation := variation.extrinsicCurvatureVariation
  measureVariation := 0
  inducedMetricVariationSymmetric :=
    variation.inducedMetricVariationSymmetric
  extrinsicCurvatureVariationSymmetric :=
    variation.extrinsicCurvatureVariationSymmetric

/-- Affine induced-metric curve in the supplied symmetric direction. -/
def inducedMetricCurve
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation)
    (t : ℝ) : Matrix3 :=
  data.inducedMetric + t • variation.inducedMetricVariation

@[simp]
theorem inducedMetricCurve_zero
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    inducedMetricCurve data variation 0 = data.inducedMetric := by
  simp [inducedMetricCurve]

/-- Relative metric tangent `h⁻¹ delta h`. -/
def relativeInducedMetricVariation
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) : Matrix3 :=
  data.inducedInverse * variation.inducedMetricVariation

/-- The inverse witness forces nonvanishing determinant. -/
theorem inducedMetric_det_ne_zero (data : NonNullBoundaryPointData) :
    Matrix.det data.inducedMetric ≠ 0 := by
  intro hZero
  have hDet := congrArg Matrix.det data.inverseWitness.mul_inverse
  rw [Matrix.det_mul, Matrix.det_one, hZero, zero_mul] at hDet
  exact zero_ne_one hDet

/-- Exact factorization used to reduce the determinant curve to a perturbation
of the identity. -/
theorem inducedMetricCurve_factor
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation)
    (t : ℝ) :
    inducedMetricCurve data variation t =
      data.inducedMetric *
        (1 + t • relativeInducedMetricVariation data variation) := by
  rw [inducedMetricCurve, relativeInducedMetricVariation, Matrix.mul_add,
    Matrix.mul_one]
  congr 1
  rw [Matrix.mul_smul, ← Matrix.mul_assoc,
    data.inverseWitness.mul_inverse, Matrix.one_mul]

/-- Quadratic coefficient in `det (1 + t A)` for a `3 x 3` matrix. -/
def determinantQuadraticCoefficient (matrix : Matrix3) : ℝ :=
  matrix 0 0 * matrix 1 1 + matrix 0 0 * matrix 2 2 +
    matrix 1 1 * matrix 2 2 - matrix 0 1 * matrix 1 0 -
    matrix 0 2 * matrix 2 0 - matrix 1 2 * matrix 2 1

/-- Exact cubic expansion of the determinant perturbation. -/
theorem det_one_add_smul_polynomial (matrix : Matrix3) (t : ℝ) :
    Matrix.det (1 + t • matrix) =
      1 + t * Matrix.trace matrix +
        (t * t) * determinantQuadraticCoefficient matrix +
        (t * t * t) * Matrix.det matrix := by
  rw [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.det_fin_three]
  simp [Matrix.add_apply, smul_eq_mul,
    determinantQuadraticCoefficient]
  ring

/-- Jacobi derivative at the identity, proved from the exact cubic
determinant rather than assumed as determinant calculus. -/
theorem det_one_add_smul_hasDerivAt (matrix : Matrix3) :
    HasDerivAt (fun t : ℝ => Matrix.det (1 + t • matrix))
      (Matrix.trace matrix) 0 := by
  have hLinear : HasDerivAt
      (fun t : ℝ => 1 + t * Matrix.trace matrix)
      (Matrix.trace matrix) 0 :=
    affineScalar_hasDerivAt 1 (Matrix.trace matrix)
  have hQuadratic : HasDerivAt
      (fun t : ℝ => (t * t) * determinantQuadraticCoefficient matrix) 0 0 := by
    have hId : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    simpa using (hId.mul hId).mul_const
      (determinantQuadraticCoefficient matrix)
  have hCubic : HasDerivAt
      (fun t : ℝ => (t * t * t) * Matrix.det matrix) 0 0 := by
    have hId : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    simpa using ((hId.mul hId).mul hId).mul_const (Matrix.det matrix)
  have hPolynomial := (hLinear.add hQuadratic).add hCubic
  exact (hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simpa only [Pi.add_apply] using
        det_one_add_smul_polynomial matrix t)).congr_deriv (by ring)

/-- Jacobi formula along the induced-metric curve. -/
theorem inducedMetricDeterminantCurve_hasDerivAt
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    HasDerivAt
      (fun t : ℝ => Matrix.det (inducedMetricCurve data variation t))
      (Matrix.det data.inducedMetric *
        Matrix.trace (relativeInducedMetricVariation data variation)) 0 := by
  have hReduced :=
    (det_one_add_smul_hasDerivAt
      (relativeInducedMetricVariation data variation)).const_mul
        (Matrix.det data.inducedMetric)
  exact hReduced.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      change Matrix.det (inducedMetricCurve data variation t) =
        Matrix.det data.inducedMetric *
          Matrix.det (1 + t • relativeInducedMetricVariation data variation)
      rw [inducedMetricCurve_factor, Matrix.det_mul])

/-- The absolute determinant derivative has no signature ambiguity: its sign
factor combines with `det h` to give `|det h|`. -/
theorem inducedMetricAbsDeterminantCurve_hasDerivAt
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    HasDerivAt
      (fun t : ℝ => |Matrix.det (inducedMetricCurve data variation t)|)
      (|Matrix.det data.inducedMetric| *
        Matrix.trace (relativeInducedMetricVariation data variation)) 0 := by
  have hDet := inducedMetricDeterminantCurve_hasDerivAt data variation
  have hDetAtZero :
      Matrix.det (inducedMetricCurve data variation 0) ≠ 0 := by
    simpa using inducedMetric_det_ne_zero data
  have hAbs :=
    (hasDerivAt_abs hDetAtZero).comp 0 hDet
  exact hAbs.congr_deriv (by
    simp only [inducedMetricCurve_zero]
    rw [← mul_assoc, sign_mul_self])

/-- Actual first variation of `sqrt |det h|`. -/
theorem inducedBoundaryMeasureCurve_hasDerivAt
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    HasDerivAt
      (fun t : ℝ =>
        Real.sqrt |Matrix.det (inducedMetricCurve data variation t)|)
      ((Real.sqrt |Matrix.det data.inducedMetric| / 2) *
        Matrix.trace (data.inducedInverse *
          variation.inducedMetricVariation)) 0 := by
  have hAbs := inducedMetricAbsDeterminantCurve_hasDerivAt data variation
  have hAbsNe : |Matrix.det data.inducedMetric| ≠ 0 :=
    abs_ne_zero.mpr (inducedMetric_det_ne_zero data)
  have hAbsAtZero :
      |Matrix.det (inducedMetricCurve data variation 0)| ≠ 0 := by
    simpa using hAbsNe
  have hSqrt := hAbs.sqrt hAbsAtZero
  have hSqrtNe : Real.sqrt |Matrix.det data.inducedMetric| ≠ 0 :=
    (Real.sqrt_ne_zero (abs_nonneg _)).mpr hAbsNe
  have hCoefficient :
      (|Matrix.det data.inducedMetric| *
          Matrix.trace (relativeInducedMetricVariation data variation)) /
          (2 * Real.sqrt
            |Matrix.det (inducedMetricCurve data variation 0)|) =
        (Real.sqrt |Matrix.det data.inducedMetric| / 2) *
          Matrix.trace (data.inducedInverse *
            variation.inducedMetricVariation) := by
    simp only [inducedMetricCurve_zero]
    rw [relativeInducedMetricVariation]
    nth_rewrite 1 [← Real.mul_self_sqrt
      (abs_nonneg (Matrix.det data.inducedMetric))]
    field_simp
  exact hSqrt.congr_deriv hCoefficient

/-- The determinant-derived measure tangent, with no independent scalar
variation slot. -/
def metricMeasureVariation
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) : ℝ :=
  (Real.sqrt |Matrix.det data.inducedMetric| / 2) *
    Matrix.trace (data.inducedInverse * variation.inducedMetricVariation)

/-- Instantiate the old variation record with the forced measure tangent. -/
def withMetricMeasureVariation
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) : NonNullGHYVariation :=
  { variation with measureVariation := metricMeasureVariation data variation }

@[simp]
theorem withMetricMeasureVariation_measureVariation
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    (withMetricMeasureVariation data variation).measureVariation =
      metricMeasureVariation data variation :=
  rfl

@[simp]
theorem withMetricMeasureVariation_meanCurvatureTraceVariation
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    meanCurvatureTraceVariation data
        (withMetricMeasureVariation data variation) =
      meanCurvatureTraceVariation data variation :=
  rfl

@[simp]
theorem withMetricMeasureVariation_inverseExtrinsicTraceCurve
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation)
    (t : ℝ) :
    inverseExtrinsicTraceCurve data
        (withMetricMeasureVariation data variation) t =
      inverseExtrinsicTraceCurve data variation t :=
  rfl

/-- First-jet GHY curve using the actual determinant measure and the affine
inverse/extrinsic tangent curve.  The inverse slot has the correct constrained
first derivative, but this is not a curve of exact inverses for `t ≠ 0`. -/
def nonNullGHYMetricFirstJetCurve
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) (t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det (inducedMetricCurve data variation t)| *
      inverseExtrinsicTraceCurve data variation t

/-- Exact derivative of the pointwise GHY metric first jet, with the measure
tangent fixed by the metric variation. -/
theorem nonNullGHYMetricFirstJetCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) :
    HasDerivAt
      (nonNullGHYMetricFirstJetCurve einsteinScale data variation)
      (nonNullGHYFirstVariation einsteinScale data
        (withMetricMeasureVariation data variation)) 0 := by
  have hMeasure := inducedBoundaryMeasureCurve_hasDerivAt data variation
  have hTrace := inverseExtrinsicTraceCurve_hasDerivAt data variation
  have hProduct := (hMeasure.mul hTrace).const_mul
    (einsteinScale * data.orientationSign)
  have hDerivative :
      einsteinScale * data.orientationSign *
          (metricMeasureVariation data variation *
              meanCurvatureTrace data +
            Real.sqrt |Matrix.det data.inducedMetric| *
              meanCurvatureTraceVariation data variation) =
        nonNullGHYFirstVariation einsteinScale data
          (withMetricMeasureVariation data variation) := by
    rw [nonNullGHYFirstVariation]
    simp only [withMetricMeasureVariation_measureVariation,
      withMetricMeasureVariation_meanCurvatureTraceVariation]
  refine (hProduct.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => ?_)
  · rw [inverseExtrinsicTraceCurve_polynomial data variation 0]
    simp
    exact hDerivative
  · simp [nonNullGHYMetricFirstJetCurve]
    ring

/-- First-jet variation record instantiated from independent metric/extrinsic
data, with its measure field forced by `sqrt |det h|`. -/
def metricFirstJetVariation
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) : NonNullGHYVariation :=
  withMetricMeasureVariation data (zeroMeasureExtension variation)

@[simp]
theorem metricFirstJetVariation_measureVariation
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    (metricFirstJetVariation data variation).measureVariation =
      (Real.sqrt |Matrix.det data.inducedMetric| / 2) *
        Matrix.trace (data.inducedInverse *
          variation.inducedMetricVariation) :=
  rfl

/-- Pointwise GHY metric first-jet curve whose public variation input contains
no measure tangent.  It agrees with the GHY density and its constrained metric
derivative at the base point; it is not claimed to be inverse-compatible for
nonzero parameter. -/
def nonNullGHYIndependentMetricFirstJetCurve
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : ℝ :=
  nonNullGHYMetricFirstJetCurve einsteinScale data
    (zeroMeasureExtension variation) t

/-- Pointwise GHY metric first-jet variation: the only supplied directions are
`delta h` and `delta K`; the measure tangent is derived. -/
theorem nonNullGHYIndependentMetricFirstJetCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    HasDerivAt
      (nonNullGHYIndependentMetricFirstJetCurve einsteinScale data variation)
      (nonNullGHYFirstVariation einsteinScale data
        (metricFirstJetVariation data variation)) 0 := by
  exact nonNullGHYMetricFirstJetCurve_hasDerivAt einsteinScale data
    (zeroMeasureExtension variation)

end

end P0EFTJanusNonNullGHYMeasureVariation
end JanusFormal
