import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoDiagonalLorentzRootChart

/-!
# First Frechet derivative of the local co-diagonal Lorentz root chart

The positive scale spectra are now placed inside their ambient finite
coordinate spaces.  On the resulting open domain this file proves genuine
Frechet differentiability of the Lorentz metric, its inverse, the positive
ratio spectrum, the root matrix, and the relative metric.  Differentiating
the exact square-root identity gives the Sylvester equation, and the explicit
positive-diagonal inverse determines the derivative of the concrete root map
without a supplied differentiability or square-root hypothesis.

All statements remain local to the co-diagonal chart.  No smooth branch on the
full Hassan--Kocic Lorentz domain is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCoDiagonalLorentzRootFirstDerivative

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusCoDiagonalLorentzRootChart

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

abbrev Spectrum4 := Fin 4 → ℝ

/-- Ambient coordinates for the two independent positive scale spectra. -/
abbrev ScalePair := Spectrum4 × Spectrum4

/-- Positive single-sector scale domain in its ambient coordinate space. -/
def ambientPositiveScaleDomain : Set Spectrum4 :=
  positiveDiagonalDomain

theorem ambientPositiveScaleDomain_isOpen :
    IsOpen ambientPositiveScaleDomain :=
  positiveDiagonalDomain_isOpen

/-- Open product domain for the independent plus/minus scale spectra. -/
def ambientPositiveScalePairDomain : Set ScalePair :=
  ambientPositiveScaleDomain ×ˢ ambientPositiveScaleDomain

theorem ambientPositiveScalePairDomain_isOpen :
    IsOpen ambientPositiveScalePairDomain :=
  ambientPositiveScaleDomain_isOpen.prod ambientPositiveScaleDomain_isOpen

/-- Ambient point represented by two positive typed spectra. -/
def positiveScalePairPoint
    (plusScales minusScales : PositiveScales) : ScalePair :=
  (plusScales.1, minusScales.1)

theorem positiveScalePairPoint_mem
    (plusScales minusScales : PositiveScales) :
    positiveScalePairPoint plusScales minusScales ∈
      ambientPositiveScalePairDomain :=
  ⟨plusScales.2, minusScales.2⟩

/-- Polynomial extension of the co-diagonal Lorentz metric to ambient scale
coordinates. -/
def ambientLorentzMetric (scales : Spectrum4) : Matrix4 :=
  Matrix.diagonal (fun i => lorentzSign i * scales i ^ 2)

/-- Rational extension of the inverse metric.  It is differentiated only on
the positive open domain. -/
def ambientLorentzMetricInverse (scales : Spectrum4) : Matrix4 :=
  Matrix.diagonal (fun i => lorentzSign i / scales i ^ 2)

/-- Ambient ratio spectrum. -/
def ambientRootRatio (point : ScalePair) : Spectrum4 :=
  fun i => point.2 i / point.1 i

/-- Concrete positive root map on the open chart. -/
def ambientRootMatrix (point : ScalePair) : Matrix4 :=
  Matrix.diagonal (ambientRootRatio point)

/-- Relative target formed from the explicit ambient metric maps. -/
def ambientRelativeMetric (point : ScalePair) : Matrix4 :=
  ambientLorentzMetricInverse point.1 * ambientLorentzMetric point.2

@[simp]
theorem ambientLorentzMetric_positiveScales (scales : PositiveScales) :
    ambientLorentzMetric scales.1 = lorentzMetric scales :=
  rfl

@[simp]
theorem ambientLorentzMetricInverse_positiveScales
    (scales : PositiveScales) :
    ambientLorentzMetricInverse scales.1 = lorentzMetricInverse scales :=
  rfl

@[simp]
theorem ambientRootRatio_positiveScales
    (plusScales minusScales : PositiveScales) :
    ambientRootRatio (positiveScalePairPoint plusScales minusScales) =
      (rootRatioSpectrum plusScales minusScales).1 :=
  rfl

@[simp]
theorem ambientRootMatrix_positiveScales
    (plusScales minusScales : PositiveScales) :
    ambientRootMatrix (positiveScalePairPoint plusScales minusScales) =
      rootMatrix plusScales minusScales :=
  rfl

/-- The polynomial metric map is Frechet differentiable everywhere. -/
theorem ambientLorentzMetric_differentiableAt (scales : Spectrum4) :
    DifferentiableAt ℝ ambientLorentzMetric scales := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  by_cases hij : i = j
  · subst j
    simp only [ambientLorentzMetric, Matrix.diagonal_apply_eq]
    fun_prop
  · simp [ambientLorentzMetric, hij]

/-- The inverse metric is Frechet differentiable at every positive scale
spectrum. -/
theorem ambientLorentzMetricInverse_differentiableAt
    (scales : Spectrum4) (hScales : scales ∈ ambientPositiveScaleDomain) :
    DifferentiableAt ℝ ambientLorentzMetricInverse scales := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  by_cases hij : i = j
  · subst j
    have hNonzero : scales i ≠ 0 := ne_of_gt (hScales i)
    simp only [ambientLorentzMetricInverse, Matrix.diagonal_apply_eq]
    fun_prop (disch := exact pow_ne_zero 2 hNonzero)
  · simp [ambientLorentzMetricInverse, hij]

/-- The ratio spectrum is Frechet differentiable on the positive product
domain. -/
theorem ambientRootRatio_differentiableAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    DifferentiableAt ℝ ambientRootRatio point := by
  unfold ambientRootRatio
  apply differentiableAt_pi.2
  intro i
  have hNonzero : point.1 i ≠ 0 := ne_of_gt (hPoint.1 i)
  fun_prop (disch := exact hNonzero)

/-- The concrete root matrix is Frechet differentiable on the positive
product domain. -/
theorem ambientRootMatrix_differentiableAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    DifferentiableAt ℝ ambientRootMatrix point := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  by_cases hij : i = j
  · subst j
    simp only [ambientRootMatrix, Matrix.diagonal_apply_eq]
    exact (differentiableAt_pi.1
      (ambientRootRatio_differentiableAt point hPoint)) i
  · simp [ambientRootMatrix, hij]

/-- The explicit relative metric is Frechet differentiable on the positive
product domain. -/
theorem ambientRelativeMetric_differentiableAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    DifferentiableAt ℝ ambientRelativeMetric point := by
  have hInverse : DifferentiableAt ℝ
      (fun varied : ScalePair => ambientLorentzMetricInverse varied.1) point :=
    (ambientLorentzMetricInverse_differentiableAt point.1 hPoint.1).comp
      point differentiableAt_fst
  have hMinus : DifferentiableAt ℝ
      (fun varied : ScalePair => ambientLorentzMetric varied.2) point :=
    (ambientLorentzMetric_differentiableAt point.2).comp
      point differentiableAt_snd
  exact hInverse.mul hMinus

/-- Actual Frechet derivative of the ambient metric map. -/
def ambientLorentzMetricDerivative
    (scales : Spectrum4) : Spectrum4 →L[ℝ] Matrix4 :=
  fderiv ℝ ambientLorentzMetric scales

/-- Actual Frechet derivative of the inverse metric map. -/
def ambientLorentzMetricInverseDerivative
    (scales : Spectrum4) : Spectrum4 →L[ℝ] Matrix4 :=
  fderiv ℝ ambientLorentzMetricInverse scales

/-- Actual Frechet derivative of the ratio spectrum. -/
def ambientRootRatioDerivative
    (point : ScalePair) : ScalePair →L[ℝ] Spectrum4 :=
  fderiv ℝ ambientRootRatio point

/-- Actual Frechet derivative of the concrete root matrix. -/
def ambientRootMatrixDerivative
    (point : ScalePair) : ScalePair →L[ℝ] Matrix4 :=
  fderiv ℝ ambientRootMatrix point

/-- Actual Frechet derivative of the explicit relative target. -/
def ambientRelativeMetricDerivative
    (point : ScalePair) : ScalePair →L[ℝ] Matrix4 :=
  fderiv ℝ ambientRelativeMetric point

theorem ambientLorentzMetric_hasFDerivAt (scales : Spectrum4) :
    HasFDerivAt ambientLorentzMetric
      (ambientLorentzMetricDerivative scales) scales :=
  (ambientLorentzMetric_differentiableAt scales).hasFDerivAt

theorem ambientLorentzMetricInverse_hasFDerivAt
    (scales : Spectrum4) (hScales : scales ∈ ambientPositiveScaleDomain) :
    HasFDerivAt ambientLorentzMetricInverse
      (ambientLorentzMetricInverseDerivative scales) scales :=
  (ambientLorentzMetricInverse_differentiableAt scales hScales).hasFDerivAt

theorem ambientRootRatio_hasFDerivAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt ambientRootRatio (ambientRootRatioDerivative point) point :=
  (ambientRootRatio_differentiableAt point hPoint).hasFDerivAt

theorem ambientRootMatrix_hasFDerivAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt ambientRootMatrix (ambientRootMatrixDerivative point) point :=
  (ambientRootMatrix_differentiableAt point hPoint).hasFDerivAt

theorem ambientRelativeMetric_hasFDerivAt
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt ambientRelativeMetric
      (ambientRelativeMetricDerivative point) point :=
  (ambientRelativeMetric_differentiableAt point hPoint).hasFDerivAt

/-- The square-root identity holds algebraically on all ambient coordinates;
outside the positive domain this is only a totalized rational identity, not a
Lorentz-chart assertion. -/
theorem ambientRoot_square_eq_relativeMetric (point : ScalePair) :
    squareMap (ambientRootMatrix point) = ambientRelativeMetric point := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hPlus : point.1 i = 0
    · simp [squareMap, ambientRootMatrix, ambientRootRatio,
        ambientRelativeMetric, ambientLorentzMetricInverse,
        ambientLorentzMetric, hPlus]
    · simp [squareMap, ambientRootMatrix, ambientRootRatio,
        ambientRelativeMetric, ambientLorentzMetricInverse,
        ambientLorentzMetric]
      field_simp [hPlus]
      have hSign : lorentzSign i ^ 2 = 1 := by
        rw [pow_two]
        exact lorentzSign_sq i
      rw [hSign, mul_one]
  · simp [squareMap, ambientRootMatrix, ambientRootRatio,
      ambientRelativeMetric, ambientLorentzMetricInverse,
      ambientLorentzMetric, hij]

/-- Differentiating the exact square-root identity gives the Sylvester
equation for the actual chart derivatives. -/
theorem ambient_squareRootIdentity_fderiv
    (point : ScalePair) (hPoint : point ∈ ambientPositiveScalePairDomain) :
    (sylvesterOperator (ambientRootMatrix point)).comp
        (ambientRootMatrixDerivative point) =
      ambientRelativeMetricDerivative point := by
  have hLeft := (squareMap_hasFDerivAt (ambientRootMatrix point)).comp point
    (ambientRootMatrix_hasFDerivAt point hPoint)
  have hRight := ambientRelativeMetric_hasFDerivAt point hPoint
  have hFunctions :
      squareMap ∘ ambientRootMatrix = ambientRelativeMetric := by
    funext varied
    exact ambientRoot_square_eq_relativeMetric varied
  rw [hFunctions] at hLeft
  exact hLeft.unique hRight

/-- The explicit co-diagonal map instantiates the positive-diagonal
Sylvester derivative with no supplied `hRoot` or `hSquare`. -/
theorem explicitCoDiagonalRoot_hasFDerivAt
    (plusScales minusScales : PositiveScales) :
    HasFDerivAt ambientRootMatrix
      ((diagonalSylvesterInverse
        (rootRatioSpectrum plusScales minusScales)).comp
          (ambientRelativeMetricDerivative
            (positiveScalePairPoint plusScales minusScales)))
      (positiveScalePairPoint plusScales minusScales) := by
  apply positiveDiagonal_squareRoot_hasFDerivAt
    (rootRatioSpectrum plusScales minusScales)
  · rfl
  · exact ambientRootMatrix_differentiableAt
      (positiveScalePairPoint plusScales minusScales)
      (positiveScalePairPoint_mem plusScales minusScales)
  · exact ambientRelativeMetric_hasFDerivAt
      (positiveScalePairPoint plusScales minusScales)
      (positiveScalePairPoint_mem plusScales minusScales)
  · intro point
    exact ambientRoot_square_eq_relativeMetric point

/-- Consequently the actual Frechet derivative of the explicit chart root is
the entrywise Sylvester inverse applied to the actual relative-metric
derivative. -/
theorem ambientRootMatrixDerivative_eq_explicitSylvester
    (plusScales minusScales : PositiveScales) :
    ambientRootMatrixDerivative
        (positiveScalePairPoint plusScales minusScales) =
      (diagonalSylvesterInverse
        (rootRatioSpectrum plusScales minusScales)).comp
          (ambientRelativeMetricDerivative
            (positiveScalePairPoint plusScales minusScales)) := by
  exact (explicitCoDiagonalRoot_hasFDerivAt
    plusScales minusScales).fderiv

end

end P0EFTJanusCoDiagonalLorentzRootFirstDerivative
end JanusFormal
