import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoDiagonalLorentzRootFirstDerivative
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionDensityCovariance
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionFrechetNoether

/-!
# Frechet derivative of the Candidate-A density on the co-diagonal chart

This file composes the actual plus-metric volume `sqrt |det gPlus|` with the
full four-dimensional spectral potential of the explicit positive root.  Its
Frechet derivative is obtained from the determinant, absolute value, square
root, root-chart, and spectral-potential derivatives, followed by the product
rule.  No interaction covector or root derivative is supplied as a hypothesis.

The result is strictly finite-dimensional and local to the positive
co-diagonal scale chart.  It is not a metric-functional variation on a
manifold and does not assert a covariant field equation.
-/

namespace JanusFormal
namespace P0EFTJanusCoDiagonalInteractionDensityFrechet

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusCoDiagonalLorentzRootChart
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
open P0EFTJanusPositiveDiagonalSylvesterInverse

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

abbrev Spectrum4 := Fin 4 → ℝ

abbrev ScalePair := Spectrum4 × Spectrum4

/-- The plus metric as a function on the ambient pair of scale spectra. -/
def ambientPlusMetric (point : ScalePair) : Matrix4 :=
  ambientLorentzMetric point.1

/-- The exact coordinate volume of the plus metric. -/
def ambientPlusMetricVolume (point : ScalePair) : ℝ :=
  Real.sqrt |Matrix.det (ambientPlusMetric point)|

/-- Candidate A restricted to the positive co-diagonal chart.  All five
elementary-symmetric coefficients remain free. -/
def coDiagonalInteractionDensity
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) : ℝ :=
  -interactionScale * ambientPlusMetricVolume point *
    matrixSpectralPotential coefficients (ambientRootMatrix point)

/-- Actual derivative of the plus-metric map, including projection onto the
plus scale spectrum. -/
def ambientPlusMetricDerivative (point : ScalePair) :
    ScalePair →L[ℝ] Matrix4 :=
  (ambientLorentzMetricDerivative point.1).comp
    (ContinuousLinearMap.fst ℝ Spectrum4 Spectrum4)

/-- Determinant derivative after the actual plus-metric derivative. -/
def ambientPlusMetricDeterminantDerivative (point : ScalePair) :
    ScalePair →L[ℝ] ℝ :=
  (determinantDerivative (ambientPlusMetric point)).comp
    (ambientPlusMetricDerivative point)

/-- Explicit chain derivative of `sqrt |det gPlus|`. -/
def ambientPlusMetricVolumeDerivative (point : ScalePair) :
    ScalePair →L[ℝ] ℝ :=
  (1 / (2 * Real.sqrt |Matrix.det (ambientPlusMetric point)|)) •
    ((SignType.sign (Matrix.det (ambientPlusMetric point)) : ℝ) •
      ambientPlusMetricDeterminantDerivative point)

/-- The full spectral-potential covector composed with the actual chart-root
derivative. -/
def coDiagonalSpectralPotentialDerivative
    (coefficients : PotentialCoefficients) (point : ScalePair) :
    ScalePair →L[ℝ] ℝ :=
  (matrixSpectralPotentialDerivative coefficients
      (ambientRootMatrix point)).comp
    (ambientRootMatrixDerivative point)

/-- Product-rule derivative of the complete co-diagonal interaction density. -/
def coDiagonalInteractionDensityDerivative
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) : ScalePair →L[ℝ] ℝ :=
  (-interactionScale * ambientPlusMetricVolume point) •
      coDiagonalSpectralPotentialDerivative coefficients point +
    matrixSpectralPotential coefficients (ambientRootMatrix point) •
      ((-interactionScale) • ambientPlusMetricVolumeDerivative point)

theorem ambientPlusMetric_hasFDerivAt (point : ScalePair) :
    HasFDerivAt ambientPlusMetric (ambientPlusMetricDerivative point) point := by
  exact (ambientLorentzMetric_hasFDerivAt point.1).comp point
    (ContinuousLinearMap.fst ℝ Spectrum4 Spectrum4).hasFDerivAt

theorem ambientPlusMetric_det_ne_zero
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    Matrix.det (ambientPlusMetric point) ≠ 0 := by
  let plusScales : PositiveScales := ⟨point.1, hPoint.1⟩
  have hNonzero := frame_det_ne_zero
    (lorentzMetric plusScales) (lorentzMetricInverse plusScales)
    (lorentzMetricInverseWitness plusScales)
  exact hNonzero

theorem ambientPlusMetricDeterminant_hasFDerivAt (point : ScalePair) :
    HasFDerivAt (fun varied => Matrix.det (ambientPlusMetric varied))
      (ambientPlusMetricDeterminantDerivative point) point := by
  have hDet := determinant_hasFDerivAt (ambientPlusMetric point)
  unfold FrobeniusHasFDerivAt at hDet
  exact hDet.comp point (ambientPlusMetric_hasFDerivAt point)

/-- The displayed volume covector is derived from the metric determinant,
absolute value, and square root. -/
theorem ambientPlusMetricVolume_hasFDerivAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt ambientPlusMetricVolume
      (ambientPlusMetricVolumeDerivative point) point := by
  have hDetNonzero := ambientPlusMetric_det_ne_zero point hPoint
  have hAbs := (ambientPlusMetricDeterminant_hasFDerivAt point).abs hDetNonzero
  have hSqrt := hAbs.sqrt (abs_ne_zero.mpr hDetNonzero)
  exact hSqrt

/-- The displayed potential derivative follows by composing the proven full
matrix covector with the proven chart-root derivative. -/
theorem coDiagonalSpectralPotential_hasFDerivAt
    (coefficients : PotentialCoefficients) (point : ScalePair)
    (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt
      (fun varied =>
        matrixSpectralPotential coefficients (ambientRootMatrix varied))
      (coDiagonalSpectralPotentialDerivative coefficients point) point := by
  have hPotential := matrixSpectralPotential_hasFDerivAt coefficients
    (ambientRootMatrix point)
  unfold FrobeniusHasFDerivAt at hPotential
  exact hPotential.comp point (ambientRootMatrix_hasFDerivAt point hPoint)

/-- The co-diagonal potential derivative uses the explicit positive-diagonal
Sylvester inverse at every typed chart point. -/
theorem coDiagonalSpectralPotentialDerivative_eq_explicitSylvester
    (coefficients : PotentialCoefficients)
    (plusScales minusScales : PositiveScales) :
    coDiagonalSpectralPotentialDerivative coefficients
        (positiveScalePairPoint plusScales minusScales) =
      (matrixSpectralPotentialDerivative coefficients
        (rootMatrix plusScales minusScales)).comp
        ((diagonalSylvesterInverse
          (rootRatioSpectrum plusScales minusScales)).comp
          (ambientRelativeMetricDerivative
            (positiveScalePairPoint plusScales minusScales))) := by
  unfold coDiagonalSpectralPotentialDerivative
  rw [ambientRootMatrixDerivative_eq_explicitSylvester]
  rfl

/-- The full Candidate-A density has the stated genuine Frechet derivative on
the open positive scale-pair domain. -/
theorem coDiagonalInteractionDensity_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt (coDiagonalInteractionDensity interactionScale coefficients)
      (coDiagonalInteractionDensityDerivative interactionScale coefficients
        point) point := by
  have hVolume := ambientPlusMetricVolume_hasFDerivAt point hPoint
  have hPotential := coDiagonalSpectralPotential_hasFDerivAt
    coefficients point hPoint
  exact (hVolume.const_mul (-interactionScale)).mul hPotential

@[simp]
theorem coDiagonalInteractionDensityDerivative_apply
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point variation : ScalePair) :
    coDiagonalInteractionDensityDerivative interactionScale coefficients
        point variation =
      (-interactionScale * ambientPlusMetricVolume point) *
          coDiagonalSpectralPotentialDerivative coefficients point variation +
        matrixSpectralPotential coefficients (ambientRootMatrix point) *
          (-interactionScale *
            ambientPlusMetricVolumeDerivative point variation) := by
  simp [coDiagonalInteractionDensityDerivative]

/-- On typed positive spectra this is exactly the committed pointwise
Candidate-A density, rather than a surrogate polynomial. -/
theorem coDiagonalInteractionDensity_eq_pointwiseCandidateA
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (plusScales minusScales : PositiveScales) :
    coDiagonalInteractionDensity interactionScale coefficients
        (positiveScalePairPoint plusScales minusScales) =
      pointwiseInteractionDensity interactionScale coefficients
        (forgetBranch
          (coDiagonalSquareRootPointData plusScales minusScales)) := by
  rfl

end

end P0EFTJanusCoDiagonalInteractionDensityFrechet
end JanusFormal
