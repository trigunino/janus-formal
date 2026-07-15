import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonNullGHYExactInverseCurve

/-!
# Exact extrinsic-trace curve for the non-null GHY density

This gate uses the actual local inverse of the affine induced metric
`h(t) = h + t delta-h` together with the affine second-fundamental-form curve
`B(t) = B + t delta-B`.  The mean-curvature trace is defined by
`K(t) = tr (h(t)⁻¹ B(t))`; its derivative is obtained from matrix inversion
and multiplication, rather than supplied as an independent `delta-K` slot.
The determinant measure is then differentiated in the same curve.

An affine normal metric jet realizes the convention
`B(t) = (1 / 2) partial_n h(t,n)|_{n=0}`.  This is only a pointwise
Gaussian-normal first jet.  Constructing an embedding, its unit normal and
the corresponding Levi-Civita second fundamental form remains open here.
-/

namespace JanusFormal
namespace P0EFTJanusNonNullGHYExtrinsicTraceCurve

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation
open P0EFTJanusNonNullGHYExactInverseCurve
open Filter Topology

abbrev Matrix3 := P0EFTJanusExplicitBoundaryDensityLedger.Matrix3

/-- The affine covariant second-fundamental-form curve `B + t delta-B`. -/
def secondFundamentalFormCurve
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : Matrix3 :=
  data.extrinsicCurvature + t • variation.extrinsicCurvatureVariation

@[simp]
theorem secondFundamentalFormCurve_zero
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    secondFundamentalFormCurve data variation 0 =
      data.extrinsicCurvature := by
  simp [secondFundamentalFormCurve]

theorem secondFundamentalFormCurve_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusMatrixHasDerivAt
      (secondFundamentalFormCurve data variation)
      variation.extrinsicCurvatureVariation 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hDerivative :=
    ((hasDerivAt_id (0 : ℝ)).smul_const
      variation.extrinsicCurvatureVariation).const_add
        data.extrinsicCurvature
  exact (hDerivative.congr_deriv
    (one_smul ℝ variation.extrinsicCurvatureVariation)).hasFDerivAt

/-- The derivative forced by differentiating `tr (h⁻¹ B)`.  There is no
independent scalar mean-curvature tangent in this definition. -/
def extrinsicTraceDerivative
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) : ℝ :=
  Matrix.trace
    (constrainedInverseVariation data (zeroMeasureExtension variation) *
        data.extrinsicCurvature +
      data.inducedInverse * variation.extrinsicCurvatureVariation)

/-- Exact trace curve `K(t) = tr (h(t)⁻¹ B(t))`. -/
def exactExtrinsicTraceCurve
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : ℝ :=
  Matrix.trace
    (exactInducedInverseCurve data variation t *
      secondFundamentalFormCurve data variation t)

@[simp]
theorem exactExtrinsicTraceCurve_zero
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    exactExtrinsicTraceCurve data variation 0 =
      meanCurvatureTrace data := by
  simp [exactExtrinsicTraceCurve, meanCurvatureTrace]

/-- The trace derivative follows from the actual inverse derivative and the
affine `B` derivative. -/
theorem exactExtrinsicTraceCurve_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusScalarHasDerivAt (exactExtrinsicTraceCurve data variation)
      (extrinsicTraceDerivative data variation) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hInverse := exactInducedInverseCurve_hasDerivAt data variation
  have hSecond := secondFundamentalFormCurve_hasDerivAt data variation
  unfold FrobeniusMatrixHasDerivAt at hInverse hSecond
  have hInverseDeriv :
      HasDerivAt (exactInducedInverseCurve data variation)
        (constrainedInverseVariation data (zeroMeasureExtension variation)) 0 :=
    hInverse.hasDerivAt.congr_deriv (by simp)
  have hSecondDeriv :
      HasDerivAt (secondFundamentalFormCurve data variation)
        variation.extrinsicCurvatureVariation 0 :=
    hSecond.hasDerivAt.congr_deriv (by simp)
  have hProduct := hInverseDeriv.mul hSecondDeriv
  have hTrace := traceCovector.hasFDerivAt.comp_hasDerivAt 0 hProduct
  have hDerivative :
      traceCovector
          (constrainedInverseVariation data (zeroMeasureExtension variation) *
              secondFundamentalFormCurve data variation 0 +
            exactInducedInverseCurve data variation 0 *
              variation.extrinsicCurvatureVariation) =
        extrinsicTraceDerivative data variation := by
    simp [traceCovector_apply, extrinsicTraceDerivative]
  have hCorrect := hTrace.congr_deriv hDerivative
  change HasFDerivAt
    (fun t : ℝ => Matrix.trace
      (exactInducedInverseCurve data variation t *
        secondFundamentalFormCurve data variation t))
    (ContinuousLinearMap.toSpanSingleton ℝ
      (extrinsicTraceDerivative data variation)) 0
  exact hCorrect.hasFDerivAt

/-- Pointwise GHY density with exact inverse, determinant measure and derived
extrinsic trace. -/
def nonNullGHYExtrinsicTraceCurve
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt
      |Matrix.det
        (inducedMetricCurve data (zeroMeasureExtension variation) t)| *
    exactExtrinsicTraceCurve data variation t

/-- Fully derived first variation of the preceding density. -/
def nonNullGHYExtrinsicTraceDerivative
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) : ℝ :=
  einsteinScale * data.orientationSign *
    (((Real.sqrt |Matrix.det data.inducedMetric| / 2) *
          Matrix.trace
            (data.inducedInverse * variation.inducedMetricVariation)) *
        meanCurvatureTrace data +
      Real.sqrt |Matrix.det data.inducedMetric| *
        extrinsicTraceDerivative data variation)

@[simp]
theorem nonNullGHYExtrinsicTraceCurve_zero
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    nonNullGHYExtrinsicTraceCurve einsteinScale data variation 0 =
      nonNullGHYDensity einsteinScale data := by
  simp [nonNullGHYExtrinsicTraceCurve, nonNullGHYDensity]

/-- The determinant measure and the trace are both differentiated from their
actual curves; no measure tangent or scalar `delta-K` is supplied. -/
theorem nonNullGHYExtrinsicTraceCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    FrobeniusScalarHasDerivAt
      (nonNullGHYExtrinsicTraceCurve einsteinScale data variation)
      (nonNullGHYExtrinsicTraceDerivative einsteinScale data variation) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hMeasure := inducedBoundaryMeasureCurve_hasDerivAt data
    (zeroMeasureExtension variation)
  have hTrace := exactExtrinsicTraceCurve_hasDerivAt data variation
  unfold FrobeniusScalarHasDerivAt at hTrace
  have hTraceDeriv :
      HasDerivAt (exactExtrinsicTraceCurve data variation)
        (extrinsicTraceDerivative data variation) 0 :=
    hTrace.hasDerivAt.congr_deriv (by simp)
  have hProduct := (hMeasure.mul hTraceDeriv).const_mul
    (einsteinScale * data.orientationSign)
  have hDerivative :
      einsteinScale * data.orientationSign *
          (((Real.sqrt |Matrix.det data.inducedMetric| / 2) *
                Matrix.trace
                  (data.inducedInverse * variation.inducedMetricVariation)) *
              meanCurvatureTrace data +
            Real.sqrt |Matrix.det data.inducedMetric| *
              extrinsicTraceDerivative data variation) =
        nonNullGHYExtrinsicTraceDerivative einsteinScale data variation := by
    rfl
  have hCorrect := hProduct.congr_deriv (by
    simpa using hDerivative)
  exact (hCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp [nonNullGHYExtrinsicTraceCurve]
      ring)).hasFDerivAt

/-- Affine Gaussian-normal metric first jet with the convention
`partial_n h = 2 B`. -/
def affineNormalMetricJet
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t normal : ℝ) : Matrix3 :=
  inducedMetricCurve data (zeroMeasureExtension variation) t +
    (2 * normal) • secondFundamentalFormCurve data variation t

@[simp]
theorem affineNormalMetricJet_normal_zero
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) :
    affineNormalMetricJet data variation t 0 =
      inducedMetricCurve data (zeroMeasureExtension variation) t := by
  simp [affineNormalMetricJet]

/-- Within the affine normal jet, `B(t)` is exactly half the normal metric
derivative.  No embedded hypersurface is asserted. -/
theorem affineNormalMetricJet_normal_hasDerivAt
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) (t : ℝ) :
    FrobeniusMatrixHasDerivAt
      (fun normal => affineNormalMetricJet data variation t normal)
      ((2 : ℝ) • secondFundamentalFormCurve data variation t) 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hNormal : HasDerivAt (fun normal : ℝ => 2 * normal) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
  have hDerivative :=
    (hNormal.smul_const
      (secondFundamentalFormCurve data variation t)).const_add
        (inducedMetricCurve data (zeroMeasureExtension variation) t)
  exact hDerivative.hasFDerivAt

/-- The true inverse identities hold locally along the metric part of the
curve used in this gate. -/
theorem eventually_exactInverseWitness
    (data : NonNullBoundaryPointData)
    (variation : NonNullGHYMetricVariation) :
    ∀ᶠ t in nhds (0 : ℝ),
      Matrix3InverseWitness
        (inducedMetricCurve data (zeroMeasureExtension variation) t)
        (exactInducedInverseCurve data variation t) :=
  eventually_exactInducedInverseCurve_inverseWitness data variation

end

end P0EFTJanusNonNullGHYExtrinsicTraceCurve
end JanusFormal
