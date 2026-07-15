import Mathlib.Tactic.FinCases
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonNullGHYExactInverseCurve

/-!
Gaussian-normal pointwise derivation of the Einstein--Hilbert boundary flux.

The normal coordinate is index zero, lapse is one, shift is zero, and the
normal has squared norm `epsilon = +1` or `epsilon = -1`.  A symmetric matrix `normalJet`
represents `partial_normal (delta h)`.  The linearized Christoffel tensor is
constructed from the full finite `4 x 4` Gaussian-normal inverse and this jet;
the Palatini vector is then contracted with the oriented unit normal.

For Dirichlet data `delta h = 0`, `delta K = normalJet / 2`.  The resulting
Einstein--Hilbert flux is proved to be the negative of the derivative of the
exact-inverse GHY curve.

This is a pointwise Gaussian-normal calculation with fixed lapse, shift and
normal.  It proves neither arbitrary-coordinate covariance nor a boundary
integration theorem.
-/

namespace JanusFormal
namespace P0EFTJanusGaussianNormalEHGHYCancellation

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation
open P0EFTJanusNonNullGHYExactInverseCurve

abbrev Matrix3 := P0EFTJanusExplicitBoundaryDensityLedger.Matrix3
abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

def normalIndex : Fin 4 := 0

def tangentIndex (index : Fin 3) : Fin 4 := index.succ

theorem sum_fin_four (function : Fin 4 → ℝ) :
    ∑ index : Fin 4, function index =
      function normalIndex + ∑ index : Fin 3, function (tangentIndex index) := by
  exact Fin.sum_univ_succ function

/-- Gaussian-normal metric with unit lapse and zero shift. -/
def gaussianMetric
    (epsilon : ℝ) (inducedMetric : Matrix3) : Matrix4 :=
  fun row column =>
    Fin.cases
      (Fin.cases epsilon (fun _ => 0) column)
      (fun tangentRow =>
        Fin.cases 0 (fun tangentColumn =>
          inducedMetric tangentRow tangentColumn) column)
      row

/-- Block inverse candidate: `g^{00}=epsilon`, `g^{0a}=0`,
`g^{ab}=h^{ab}`. -/
def gaussianInverse
    (epsilon : ℝ) (inducedInverse : Matrix3) : Matrix4 :=
  fun row column =>
    Fin.cases
      (Fin.cases epsilon (fun _ => 0) column)
      (fun tangentRow =>
        Fin.cases 0 (fun tangentColumn =>
          inducedInverse tangentRow tangentColumn) column)
      row

@[simp]
theorem gaussianMetric_normal_normal
    (epsilon : ℝ) (metric : Matrix3) :
    gaussianMetric epsilon metric normalIndex normalIndex = epsilon :=
  rfl

@[simp]
theorem gaussianMetric_normal_tangent
    (epsilon : ℝ) (metric : Matrix3) (column : Fin 3) :
    gaussianMetric epsilon metric normalIndex (tangentIndex column) = 0 :=
  rfl

@[simp]
theorem gaussianMetric_tangent_normal
    (epsilon : ℝ) (metric : Matrix3) (row : Fin 3) :
    gaussianMetric epsilon metric (tangentIndex row) normalIndex = 0 :=
  rfl

@[simp]
theorem gaussianMetric_tangent_tangent
    (epsilon : ℝ) (metric : Matrix3) (row column : Fin 3) :
    gaussianMetric epsilon metric (tangentIndex row) (tangentIndex column) =
      metric row column :=
  rfl

@[simp]
theorem gaussianInverse_normal_normal
    (epsilon : ℝ) (inverse : Matrix3) :
    gaussianInverse epsilon inverse normalIndex normalIndex = epsilon :=
  rfl

@[simp]
theorem gaussianInverse_normal_tangent
    (epsilon : ℝ) (inverse : Matrix3) (column : Fin 3) :
    gaussianInverse epsilon inverse normalIndex (tangentIndex column) = 0 :=
  rfl

@[simp]
theorem gaussianInverse_tangent_normal
    (epsilon : ℝ) (inverse : Matrix3) (row : Fin 3) :
    gaussianInverse epsilon inverse (tangentIndex row) normalIndex = 0 :=
  rfl

@[simp]
theorem gaussianInverse_tangent_tangent
    (epsilon : ℝ) (inverse : Matrix3) (row column : Fin 3) :
    gaussianInverse epsilon inverse (tangentIndex row) (tangentIndex column) =
      inverse row column :=
  rfl

@[simp]
theorem gaussianMetric_zero_zero
    (epsilon : ℝ) (metric : Matrix3) :
    gaussianMetric epsilon metric 0 0 = epsilon :=
  rfl

@[simp]
theorem gaussianMetric_zero_succ
    (epsilon : ℝ) (metric : Matrix3) (column : Fin 3) :
    gaussianMetric epsilon metric 0 column.succ = 0 :=
  rfl

@[simp]
theorem gaussianMetric_succ_zero
    (epsilon : ℝ) (metric : Matrix3) (row : Fin 3) :
    gaussianMetric epsilon metric row.succ 0 = 0 :=
  rfl

@[simp]
theorem gaussianMetric_succ_succ
    (epsilon : ℝ) (metric : Matrix3) (row column : Fin 3) :
    gaussianMetric epsilon metric row.succ column.succ = metric row column :=
  rfl

@[simp]
theorem gaussianInverse_zero_zero
    (epsilon : ℝ) (inverse : Matrix3) :
    gaussianInverse epsilon inverse 0 0 = epsilon :=
  rfl

@[simp]
theorem gaussianInverse_zero_succ
    (epsilon : ℝ) (inverse : Matrix3) (column : Fin 3) :
    gaussianInverse epsilon inverse 0 column.succ = 0 :=
  rfl

@[simp]
theorem gaussianInverse_succ_zero
    (epsilon : ℝ) (inverse : Matrix3) (row : Fin 3) :
    gaussianInverse epsilon inverse row.succ 0 = 0 :=
  rfl

@[simp]
theorem gaussianInverse_succ_succ
    (epsilon : ℝ) (inverse : Matrix3) (row column : Fin 3) :
    gaussianInverse epsilon inverse row.succ column.succ = inverse row column :=
  rfl

theorem orientationSign_mul_self
    (epsilon : ℝ) (hSign : IsOrientationSign epsilon) :
    epsilon * epsilon = 1 := by
  rcases hSign with rfl | rfl <;> norm_num

theorem gaussianInverse_mul_gaussianMetric
    (data : NonNullBoundaryPointData) :
    gaussianInverse data.orientationSign data.inducedInverse *
        gaussianMetric data.orientationSign data.inducedMetric = 1 := by
  ext row column
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [Matrix.mul_apply, sum_fin_four, normalIndex, tangentIndex,
        orientationSign_mul_self data.orientationSign
          data.orientationSignAdmissible]
    · simp [Matrix.mul_apply, Matrix.one_apply, sum_fin_four, normalIndex, tangentIndex]
      exact ne_of_lt (Fin.succ_pos tangentColumn)
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [Matrix.mul_apply, sum_fin_four, normalIndex, tangentIndex]
    · have hEntry := congrFun
        (congrFun data.inverseWitness.inverse_mul tangentRow) tangentColumn
      simpa [Matrix.mul_apply, Matrix.one_apply, sum_fin_four, normalIndex,
        tangentIndex] using hEntry

theorem gaussianMetric_mul_gaussianInverse
    (data : NonNullBoundaryPointData) :
    gaussianMetric data.orientationSign data.inducedMetric *
        gaussianInverse data.orientationSign data.inducedInverse = 1 := by
  ext row column
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [Matrix.mul_apply, sum_fin_four, normalIndex, tangentIndex,
        orientationSign_mul_self data.orientationSign
          data.orientationSignAdmissible]
    · simp [Matrix.mul_apply, Matrix.one_apply, sum_fin_four, normalIndex, tangentIndex]
      exact ne_of_lt (Fin.succ_pos tangentColumn)
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [Matrix.mul_apply, sum_fin_four, normalIndex, tangentIndex]
    · have hEntry := congrFun
        (congrFun data.inverseWitness.mul_inverse tangentRow) tangentColumn
      simpa [Matrix.mul_apply, Matrix.one_apply, sum_fin_four, normalIndex,
        tangentIndex] using hEntry

/-- Normal derivative jet `partial_mu (delta g_nu rho)`.  Only
`partial_0 (delta g_ab)` is nonzero. -/
def normalMetricVariationJet
    (normalJet : Matrix3) (derivative row column : Fin 4) : ℝ :=
  Fin.cases
    (Fin.cases 0 (fun tangentRow =>
      Fin.cases 0 (fun tangentColumn =>
        normalJet tangentRow tangentColumn) column) row)
    (fun _ => 0)
    derivative

@[simp]
theorem normalMetricVariationJet_normal_tangent_tangent
    (normalJet : Matrix3) (row column : Fin 3) :
    normalMetricVariationJet normalJet normalIndex
        (tangentIndex row) (tangentIndex column) = normalJet row column :=
  rfl

@[simp]
theorem normalMetricVariationJet_tangent
    (normalJet : Matrix3) (derivative : Fin 3) (row column : Fin 4) :
    normalMetricVariationJet normalJet (tangentIndex derivative) row column = 0 :=
  rfl

@[simp]
theorem normalMetricVariationJet_normal_normal_left
    (normalJet : Matrix3) (column : Fin 4) :
    normalMetricVariationJet normalJet normalIndex normalIndex column = 0 := by
  fin_cases column <;> rfl

@[simp]
theorem normalMetricVariationJet_normal_normal_right
    (normalJet : Matrix3) (row : Fin 4) :
    normalMetricVariationJet normalJet normalIndex row normalIndex = 0 := by
  fin_cases row <;> rfl

/-- Linearized Levi-Civita Christoffel tensor at the Gaussian-normal point. -/
def linearizedChristoffel
    (epsilon : ℝ) (inducedInverse normalJet : Matrix3)
    (upper lowerLeft lowerRight : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ contracted : Fin 4,
    gaussianInverse epsilon inducedInverse upper contracted *
      (normalMetricVariationJet normalJet lowerLeft contracted lowerRight +
        normalMetricVariationJet normalJet lowerRight contracted lowerLeft -
        normalMetricVariationJet normalJet contracted lowerLeft lowerRight)

@[simp]
theorem linearizedChristoffel_normal_normal_normal
    (epsilon : ℝ) (inverse normalJet : Matrix3) :
    linearizedChristoffel epsilon inverse normalJet
      normalIndex normalIndex normalIndex = 0 := by
  rw [linearizedChristoffel, sum_fin_four]
  simp

@[simp]
theorem linearizedChristoffel_normal_tangent_tangent
    (epsilon : ℝ) (inverse normalJet : Matrix3)
    (row column : Fin 3) :
    linearizedChristoffel epsilon inverse normalJet normalIndex
        (tangentIndex row) (tangentIndex column) =
      -(epsilon / 2) * normalJet row column := by
  rw [linearizedChristoffel, sum_fin_four]
  simp
  ring

@[simp]
theorem linearizedChristoffel_tangent_normal_tangent
    (epsilon : ℝ) (inverse normalJet : Matrix3)
    (upper column : Fin 3) :
    linearizedChristoffel epsilon inverse normalJet (tangentIndex upper)
        normalIndex (tangentIndex column) =
      (1 / 2 : ℝ) * ∑ contracted : Fin 3,
        inverse upper contracted * normalJet contracted column := by
  rw [linearizedChristoffel, sum_fin_four]
  simp

/-- First contraction `g^{mu nu} delta Gamma^0_{mu nu}`. -/
def palatiniFirstTrace
    (epsilon : ℝ) (inverse normalJet : Matrix3) : ℝ :=
  ∑ lowerLeft : Fin 4, ∑ lowerRight : Fin 4,
    gaussianInverse epsilon inverse lowerLeft lowerRight *
      linearizedChristoffel epsilon inverse normalJet normalIndex
        lowerLeft lowerRight

/-- Second contraction `g^{0 mu} delta Gamma^nu_{mu nu}`. -/
def palatiniSecondTrace
    (epsilon : ℝ) (inverse normalJet : Matrix3) : ℝ :=
  ∑ lowerLeft : Fin 4, ∑ upper : Fin 4,
    gaussianInverse epsilon inverse normalIndex lowerLeft *
      linearizedChristoffel epsilon inverse normalJet upper lowerLeft upper

/-- Normal component of the Palatini vector
`V^rho = g^{mu nu} delta Gamma^rho_{mu nu}
         - g^{rho mu} delta Gamma^nu_{mu nu}`. -/
def palatiniNormalVector
    (epsilon : ℝ) (inverse normalJet : Matrix3) : ℝ :=
  palatiniFirstTrace epsilon inverse normalJet -
    palatiniSecondTrace epsilon inverse normalJet

theorem palatiniFirstTrace_eq
    (epsilon : ℝ) (inverse normalJet : Matrix3) :
    palatiniFirstTrace epsilon inverse normalJet =
      -(epsilon / 2) * Matrix.trace (inverse * normalJet.transpose) := by
  simp only [palatiniFirstTrace, sum_fin_four]
  simp [linearizedChristoffel_normal_normal_normal,
    linearizedChristoffel_normal_tangent_tangent]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ]
  ring

theorem palatiniSecondTrace_eq
    (epsilon : ℝ) (inverse normalJet : Matrix3) :
    palatiniSecondTrace epsilon inverse normalJet =
      (epsilon / 2) * Matrix.trace (inverse * normalJet) := by
  simp only [palatiniSecondTrace, sum_fin_four]
  simp [linearizedChristoffel_normal_normal_normal,
    linearizedChristoffel_tangent_normal_tangent]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem palatiniNormalVector_eq
    (epsilon : ℝ) (inverse normalJet : Matrix3)
    (hSymmetric : normalJet.transpose = normalJet) :
    palatiniNormalVector epsilon inverse normalJet =
      -epsilon * Matrix.trace (inverse * normalJet) := by
  rw [palatiniNormalVector, palatiniFirstTrace_eq,
    palatiniSecondTrace_eq, hSymmetric]
  ring

/-- The Stokes orientation factor is `epsilon`, while the normal covector has
component `n_0 = epsilon`; hence their product is `epsilon^2`. -/
def stokesContractedPalatini
    (epsilon : ℝ) (inverse normalJet : Matrix3) : ℝ :=
  epsilon * epsilon * palatiniNormalVector epsilon inverse normalJet

theorem stokesContractedPalatini_eq
    (epsilon : ℝ) (inverse normalJet : Matrix3)
    (hSign : IsOrientationSign epsilon)
    (hSymmetric : normalJet.transpose = normalJet) :
    stokesContractedPalatini epsilon inverse normalJet =
      -epsilon * Matrix.trace (inverse * normalJet) := by
  rw [stokesContractedPalatini, orientationSign_mul_self epsilon hSign,
    one_mul, palatiniNormalVector_eq epsilon inverse normalJet hSymmetric]

theorem stokesContractedPalatini_plus_sign
    (inverse normalJet : Matrix3)
    (hSymmetric : normalJet.transpose = normalJet) :
    stokesContractedPalatini 1 inverse normalJet =
      -Matrix.trace (inverse * normalJet) := by
  simpa using stokesContractedPalatini_eq 1 inverse normalJet
    (Or.inl rfl) hSymmetric

theorem stokesContractedPalatini_minus_sign
    (inverse normalJet : Matrix3)
    (hSymmetric : normalJet.transpose = normalJet) :
    stokesContractedPalatini (-1) inverse normalJet =
      Matrix.trace (inverse * normalJet) := by
  simpa using stokesContractedPalatini_eq (-1) inverse normalJet
    (Or.inr rfl) hSymmetric

/-- Independent Gaussian-normal Dirichlet jet. -/
structure GaussianNormalDirichletJet where
  normalMetricVariation : Matrix3
  normalMetricVariationSymmetric :
    normalMetricVariation.transpose = normalMetricVariation

/-- `delta h = 0` and `delta K = partial_normal(delta h)/2`. -/
def gaussianDirichletBoundaryVariation
    (jet : GaussianNormalDirichletJet) : NonNullGHYMetricVariation where
  inducedMetricVariation := 0
  extrinsicCurvatureVariation := (1 / 2 : ℝ) • jet.normalMetricVariation
  inducedMetricVariationSymmetric := by simp
  extrinsicCurvatureVariationSymmetric := by
    simp [Matrix.transpose_smul, jet.normalMetricVariationSymmetric]

/-- Boundary density obtained from the explicitly constructed Palatini vector
for an EH coefficient `einsteinScale / 2`. -/
def einsteinHilbertDirichletBoundaryFlux
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) : ℝ :=
  (einsteinScale / 2) *
    Real.sqrt |Matrix.det data.inducedMetric| *
      stokesContractedPalatini data.orientationSign data.inducedInverse
        jet.normalMetricVariation

theorem einsteinHilbertDirichletBoundaryFlux_eq
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    einsteinHilbertDirichletBoundaryFlux einsteinScale data jet =
      -(einsteinScale * data.orientationSign *
        (Real.sqrt |Matrix.det data.inducedMetric| / 2) *
          Matrix.trace
            (data.inducedInverse * jet.normalMetricVariation)) := by
  rw [einsteinHilbertDirichletBoundaryFlux,
    stokesContractedPalatini_eq data.orientationSign data.inducedInverse
      jet.normalMetricVariation data.orientationSignAdmissible
      jet.normalMetricVariationSymmetric]
  ring

theorem exactGHYDirichletDerivative_eq
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    nonNullGHYFirstVariation einsteinScale data
        (metricFirstJetVariation data
          (gaussianDirichletBoundaryVariation jet)) =
      einsteinScale * data.orientationSign *
        (Real.sqrt |Matrix.det data.inducedMetric| / 2) *
          Matrix.trace
            (data.inducedInverse * jet.normalMetricVariation) := by
  let variation := metricFirstJetVariation data
    (gaussianDirichletBoundaryVariation jet)
  have hMetric : variation.inducedMetricVariation = 0 := rfl
  have hMeasure : variation.measureVariation = 0 := by
    simp [variation, metricFirstJetVariation, metricMeasureVariation,
      gaussianDirichletBoundaryVariation]
  have hExtrinsic : variation.extrinsicCurvatureVariation =
      (1 / 2 : ℝ) • jet.normalMetricVariation := rfl
  rw [firstVariation_eq_fixedGeometry_of_metric_measure_zero
    einsteinScale data variation hMetric hMeasure]
  rw [hExtrinsic]
  simp [nonNullGHYExtrinsicVariation]
  ring

/-- Pointwise physical cancellation in Gaussian-normal Dirichlet gauge. -/
theorem einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    einsteinHilbertDirichletBoundaryFlux einsteinScale data jet +
      nonNullGHYFirstVariation einsteinScale data
        (metricFirstJetVariation data
          (gaussianDirichletBoundaryVariation jet)) = 0 := by
  rw [einsteinHilbertDirichletBoundaryFlux_eq,
    exactGHYDirichletDerivative_eq]
  ring

/-- The actual exact-inverse GHY curve differentiates to the negative of the
derived Gaussian-normal Einstein--Hilbert boundary flux. -/
theorem exactGHYCurve_hasDerivative_neg_einsteinHilbertFlux
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    FrobeniusScalarHasDerivAt
      (nonNullGHYExactInverseCurve einsteinScale data
        (gaussianDirichletBoundaryVariation jet))
      (-einsteinHilbertDirichletBoundaryFlux einsteinScale data jet) 0 := by
  have hCurve := nonNullGHYExactInverseCurve_hasDerivAt einsteinScale data
    (gaussianDirichletBoundaryVariation jet)
  have hDerivative :=
    einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
      einsteinScale data jet
  have hEq :
      nonNullGHYFirstVariation einsteinScale data
          (metricFirstJetVariation data
            (gaussianDirichletBoundaryVariation jet)) =
        -einsteinHilbertDirichletBoundaryFlux einsteinScale data jet := by
    linarith
  unfold FrobeniusScalarHasDerivAt at hCurve ⊢
  simpa [hEq] using hCurve

end

end P0EFTJanusGaussianNormalEHGHYCancellation
end JanusFormal
