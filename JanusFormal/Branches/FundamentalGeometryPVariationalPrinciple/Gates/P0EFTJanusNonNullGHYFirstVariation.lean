import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLocalVariations

/-!
First-order non-null GHY variation beyond the fixed-geometry slot.

The induced inverse and extrinsic curvature are varied together.  The inverse
variation is derived from the metric variation and satisfies both linearized
inverse identities.  The boundary measure is represented by its scalar first
variation; deriving that scalar from the determinant is deliberately kept as
the next gate.

This is a pointwise first-order identity.  It does not derive the bulk
Einstein--Hilbert flux or integrate a boundary face.
-/

namespace JanusFormal
namespace P0EFTJanusNonNullGHYFirstVariation

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations

/-- Symmetric metric/extrinsic variations and one supplied measure tangent. -/
structure NonNullGHYVariation where
  inducedMetricVariation : Matrix3
  extrinsicCurvatureVariation : Matrix3
  measureVariation : ℝ
  inducedMetricVariationSymmetric :
    inducedMetricVariation.transpose = inducedMetricVariation
  extrinsicCurvatureVariationSymmetric :
    extrinsicCurvatureVariation.transpose = extrinsicCurvatureVariation

/-- Derivative of the inverse metric forced by `h⁻¹ h = 1`. -/
def constrainedInverseVariation
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) : Matrix3 :=
  -(data.inducedInverse * variation.inducedMetricVariation * data.inducedInverse)

theorem constrainedInverseVariation_mul_metric_add
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    constrainedInverseVariation data variation * data.inducedMetric +
        data.inducedInverse * variation.inducedMetricVariation = 0 := by
  rw [constrainedInverseVariation]
  simp only [neg_mul, Matrix.mul_assoc, data.inverseWitness.inverse_mul,
    Matrix.mul_one]
  exact neg_add_cancel _

theorem metric_mul_constrainedInverseVariation_add
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    variation.inducedMetricVariation * data.inducedInverse +
        data.inducedMetric * constrainedInverseVariation data variation = 0 := by
  rw [constrainedInverseVariation]
  simp only [Matrix.mul_neg, ← Matrix.mul_assoc,
    data.inverseWitness.mul_inverse, Matrix.one_mul]
  exact add_neg_cancel _

def meanCurvatureTraceVariation
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) : ℝ :=
  Matrix.trace
    (constrainedInverseVariation data variation * data.extrinsicCurvature +
      data.inducedInverse * variation.extrinsicCurvatureVariation)

def quadraticTraceCoefficient
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) : ℝ :=
  Matrix.trace
    (constrainedInverseVariation data variation *
      variation.extrinsicCurvatureVariation)

def inverseExtrinsicTraceCurve
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation)
    (t : ℝ) : ℝ :=
  Matrix.trace
    ((data.inducedInverse + t • constrainedInverseVariation data variation) *
      (data.extrinsicCurvature + t •
        variation.extrinsicCurvatureVariation))

theorem inverseExtrinsicTraceCurve_polynomial
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation)
    (t : ℝ) :
    inverseExtrinsicTraceCurve data variation t =
      meanCurvatureTrace data +
        t * meanCurvatureTraceVariation data variation +
        (t * t) * quadraticTraceCoefficient data variation := by
  simp [inverseExtrinsicTraceCurve, meanCurvatureTrace,
    meanCurvatureTraceVariation, quadraticTraceCoefficient, add_mul, mul_add,
    smul_eq_mul]
  ring

theorem inverseExtrinsicTraceCurve_hasDerivAt
    (data : NonNullBoundaryPointData) (variation : NonNullGHYVariation) :
    HasDerivAt (inverseExtrinsicTraceCurve data variation)
      (meanCurvatureTraceVariation data variation) 0 := by
  have hLinear : HasDerivAt
      (fun t : ℝ => meanCurvatureTrace data +
        t * meanCurvatureTraceVariation data variation)
      (meanCurvatureTraceVariation data variation) 0 :=
    affineScalar_hasDerivAt (meanCurvatureTrace data)
      (meanCurvatureTraceVariation data variation)
  have hQuadratic : HasDerivAt
      (fun t : ℝ => (t * t) * quadraticTraceCoefficient data variation) 0 0 := by
    have hId : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    simpa using (hId.mul hId).mul_const
      (quadraticTraceCoefficient data variation)
  have hPolynomial := hLinear.add hQuadratic
  have hCurve := hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      inverseExtrinsicTraceCurve_polynomial data variation t)
  exact hCurve.congr_deriv (add_zero _)

/-- GHY density curve with compatible inverse/extrinsic tangents and an
affine supplied measure tangent. -/
def nonNullGHYFirstVariationCurve
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) (t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    (Real.sqrt |Matrix.det data.inducedMetric| + t * variation.measureVariation) *
    inverseExtrinsicTraceCurve data variation t

def nonNullGHYFirstVariation
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) : ℝ :=
  einsteinScale * data.orientationSign *
    (variation.measureVariation * meanCurvatureTrace data +
      Real.sqrt |Matrix.det data.inducedMetric| *
        meanCurvatureTraceVariation data variation)

theorem nonNullGHYFirstVariationCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation) :
    HasDerivAt
      (nonNullGHYFirstVariationCurve einsteinScale data variation)
      (nonNullGHYFirstVariation einsteinScale data variation) 0 := by
  have hMeasure := affineScalar_hasDerivAt
    (Real.sqrt |Matrix.det data.inducedMetric|) variation.measureVariation
  have hTrace := inverseExtrinsicTraceCurve_hasDerivAt data variation
  have hProduct := hMeasure.mul hTrace
  have hScaled := hProduct.const_mul
    (einsteinScale * data.orientationSign)
  have hDerivativeEq :
      einsteinScale * data.orientationSign *
          (variation.measureVariation *
              inverseExtrinsicTraceCurve data variation 0 +
            (Real.sqrt |Matrix.det data.inducedMetric| +
                0 * variation.measureVariation) *
              meanCurvatureTraceVariation data variation) =
        nonNullGHYFirstVariation einsteinScale data variation := by
    rw [inverseExtrinsicTraceCurve_polynomial data variation 0]
    simp [nonNullGHYFirstVariation]
  have hCorrect := hScaled.congr_deriv hDerivativeEq
  exact hCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp [nonNullGHYFirstVariationCurve]
      ring)

/-- If only the extrinsic curvature varies, the new formula reduces to the
previous fixed-geometry derivative. -/
theorem firstVariation_eq_fixedGeometry_of_metric_measure_zero
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYVariation)
    (hMetric : variation.inducedMetricVariation = 0)
    (hMeasure : variation.measureVariation = 0) :
    nonNullGHYFirstVariation einsteinScale data variation =
      nonNullGHYExtrinsicVariation einsteinScale data
        variation.extrinsicCurvatureVariation := by
  simp [nonNullGHYFirstVariation, meanCurvatureTraceVariation,
    constrainedInverseVariation, nonNullGHYExtrinsicVariation,
    hMetric, hMeasure]
  ring

end

end P0EFTJanusNonNullGHYFirstVariation
end JanusFormal
