import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-!
# A two-dimensional Lorentz square-root chart

In null coordinates, this gate starts from two independently supplied real
symmetric metrics

`gPlus = [[0,1],[1,0]]`,  `gMinus = [[p,q],[q,r]]`.

Their relative matrix is `A = gPlus⁻¹ gMinus = [[q,r],[p,q]]`.  On the open
domain

`det A = q² - p r > 0`,  `tr A + 2 sqrt(det A) > 0`,

the Cayley--Hamilton expression

`X = (A + sqrt(det A) I) / sqrt(tr A + 2 sqrt(det A))`

is real and satisfies `X² = A`.  The determinants certify that both supplied
metrics are nondegenerate Lorentz forms in dimension two.  This is a genuine
three-parameter chart, including diagonalizable and Jordan points, but it is
not a construction of a global principal branch, a uniqueness theorem, or a
four-dimensional result.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzPrincipalRootChart2D

set_option autoImplicit false

noncomputable section

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Fixed Lorentz metric in null coordinates; it is its own inverse. -/
def plusMetric : Matrix2 := !![0, 1; 1, 0]

def plusMetricInverse : Matrix2 := !![0, 1; 1, 0]

/-- Independently supplied symmetric second metric. -/
def minusMetric (p q r : ℝ) : Matrix2 := !![p, q; q, r]

/-- Relative endomorphism derived from the metric pair. -/
def relativeMatrix (p q r : ℝ) : Matrix2 := !![q, r; p, q]

/-- Determinant of the relative endomorphism. -/
def relativeDiscriminant (p q r : ℝ) : ℝ := q ^ 2 - p * r

/-- Radicand in the Cayley--Hamilton square-root denominator. -/
def rootRadicand (p q r : ℝ) : ℝ :=
  2 * q + 2 * Real.sqrt (relativeDiscriminant p q r)

/-- Open real chart on which the displayed square-root formula is defined. -/
def RootChartCondition (p q r : ℝ) : Prop :=
  0 < relativeDiscriminant p q r ∧ 0 < rootRadicand p q r

/-- Positive denominator selected on the chart. -/
def rootDenominator (p q r : ℝ) : ℝ :=
  Real.sqrt (rootRadicand p q r)

/-- Entrywise form of the Cayley--Hamilton root. -/
def chartRoot (p q r : ℝ) : Matrix2 :=
  !![(q + Real.sqrt (relativeDiscriminant p q r)) /
        rootDenominator p q r,
      r / rootDenominator p q r;
     p / rootDenominator p q r,
      (q + Real.sqrt (relativeDiscriminant p q r)) /
        rootDenominator p q r]

theorem plusMetric_symmetric : plusMetric.transpose = plusMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetric, Matrix.transpose_apply]

theorem minusMetric_symmetric (p q r : ℝ) :
    (minusMetric p q r).transpose = minusMetric p q r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusMetric, Matrix.transpose_apply]

theorem plusMetricInverse_mul_plusMetric :
    plusMetricInverse * plusMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetricInverse, plusMetric, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem plusMetric_mul_inverse :
    plusMetric * plusMetricInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetricInverse, plusMetric, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem plusMetric_det : Matrix.det plusMetric = -1 := by
  norm_num [plusMetric, Matrix.det_fin_two]

theorem minusMetric_det (p q r : ℝ) :
    Matrix.det (minusMetric p q r) =
      -relativeDiscriminant p q r := by
  rw [Matrix.det_fin_two]
  simp [minusMetric, relativeDiscriminant]
  ring

theorem relativeMatrix_is_metric_relative (p q r : ℝ) :
    plusMetricInverse * minusMetric p q r = relativeMatrix p q r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusMetricInverse, minusMetric, relativeMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem relativeMatrix_det (p q r : ℝ) :
    Matrix.det (relativeMatrix p q r) = relativeDiscriminant p q r := by
  rw [Matrix.det_fin_two]
  simp [relativeMatrix, relativeDiscriminant]
  ring

theorem relativeMatrix_trace (p q r : ℝ) :
    Matrix.trace (relativeMatrix p q r) = 2 * q := by
  rw [Matrix.trace_fin_two]
  simp [relativeMatrix]
  ring

theorem rootRadicand_eq_trace_add (p q r : ℝ) :
    rootRadicand p q r =
      Matrix.trace (relativeMatrix p q r) +
        2 * Real.sqrt (Matrix.det (relativeMatrix p q r)) := by
  rw [relativeMatrix_trace, relativeMatrix_det]
  rfl

theorem plusMetric_lorentzByDet :
    plusMetric.transpose = plusMetric ∧ Matrix.det plusMetric < 0 := by
  rw [plusMetric_symmetric, plusMetric_det]
  norm_num

theorem minusMetric_lorentzByDet
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    (minusMetric p q r).transpose = minusMetric p q r ∧
      Matrix.det (minusMetric p q r) < 0 := by
  constructor
  · exact minusMetric_symmetric p q r
  · rw [minusMetric_det]
    exact neg_neg_iff_pos.mpr hChart.1

theorem plusMetric_nondegenerate : Matrix.det plusMetric ≠ 0 := by
  rw [plusMetric_det]
  norm_num

theorem minusMetric_nondegenerate
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Matrix.det (minusMetric p q r) ≠ 0 := by
  exact ne_of_lt (minusMetric_lorentzByDet hChart).2

theorem relativeMatrix_nondegenerate
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Matrix.det (relativeMatrix p q r) ≠ 0 := by
  rw [relativeMatrix_det]
  exact ne_of_gt hChart.1

theorem rootDenominator_pos
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    0 < rootDenominator p q r := by
  exact Real.sqrt_pos.2 hChart.2

theorem rootDenominator_ne_zero
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    rootDenominator p q r ≠ 0 :=
  ne_of_gt (rootDenominator_pos hChart)

theorem sqrt_discriminant_square
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Real.sqrt (relativeDiscriminant p q r) ^ 2 =
      relativeDiscriminant p q r := by
  exact Real.sq_sqrt (le_of_lt hChart.1)

theorem rootDenominator_square
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    rootDenominator p q r ^ 2 = rootRadicand p q r := by
  exact Real.sq_sqrt (le_of_lt hChart.2)

/-- The entrywise definition is exactly the Cayley--Hamilton formula. -/
theorem chartRoot_eq_cayleyHamilton_formula (p q r : ℝ) :
    chartRoot p q r =
      (rootDenominator p q r)⁻¹ •
        (relativeMatrix p q r +
          Real.sqrt (relativeDiscriminant p q r) • (1 : Matrix2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartRoot, relativeMatrix, div_eq_mul_inv, mul_comm]

/-- Cayley--Hamilton gives the exact square identity throughout the chart. -/
theorem chartRoot_square
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    chartRoot p q r * chartRoot p q r = relativeMatrix p q r := by
  have hDenominator := rootDenominator_square hChart
  have hDiscriminant := sqrt_discriminant_square hChart
  have hNonzero := rootDenominator_ne_zero hChart
  simp only [relativeDiscriminant] at hDiscriminant
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartRoot, relativeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    field_simp [hNonzero]
    rw [hDenominator]
    simp only [rootRadicand, relativeDiscriminant]
    nlinarith [hDiscriminant]

theorem chartRoot_square_eq_metricRelative
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    chartRoot p q r * chartRoot p q r =
      plusMetricInverse * minusMetric p q r := by
  rw [chartRoot_square hChart, relativeMatrix_is_metric_relative]

/-- The selected chart root has positive determinant. -/
theorem chartRoot_det
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Matrix.det (chartRoot p q r) =
      Real.sqrt (relativeDiscriminant p q r) := by
  have hDenominator := rootDenominator_square hChart
  have hDiscriminant := sqrt_discriminant_square hChart
  have hNonzero := rootDenominator_ne_zero hChart
  simp only [relativeDiscriminant] at hDiscriminant
  rw [Matrix.det_fin_two]
  simp [chartRoot]
  field_simp [hNonzero]
  rw [hDenominator]
  simp only [rootRadicand, relativeDiscriminant]
  nlinarith [hDiscriminant]

theorem chartRoot_det_pos
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    0 < Matrix.det (chartRoot p q r) := by
  rw [chartRoot_det hChart]
  exact Real.sqrt_pos.2 hChart.1

/-- On the chart, the root trace equals the positive denominator. -/
theorem chartRoot_trace
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Matrix.trace (chartRoot p q r) = rootDenominator p q r := by
  have hDenominator := rootDenominator_square hChart
  have hNonzero := rootDenominator_ne_zero hChart
  rw [Matrix.trace_fin_two]
  simp [chartRoot]
  field_simp [hNonzero]
  rw [hDenominator]
  simp only [rootRadicand]
  ring

/-- The Cayley--Hamilton formula varies continuously at every chart point. -/
theorem chartRoot_continuousAt
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    ContinuousAt
      (fun point : ℝ × ℝ × ℝ =>
        chartRoot point.1 point.2.1 point.2.2)
      (p, q, r) := by
  have hNonzero : rootDenominator p q r ≠ 0 :=
    rootDenominator_ne_zero hChart
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [chartRoot]
  all_goals
    apply ContinuousAt.div
    · try simp only [relativeDiscriminant]
      fun_prop
    · simp only [rootDenominator, rootRadicand, relativeDiscriminant]
      fun_prop
    · simpa using hNonzero

/-- Combined chart certificate, deliberately local to real dimension two. -/
theorem lorentzPrincipalRootChart2D_gate
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    plusMetric.transpose = plusMetric ∧
      (minusMetric p q r).transpose = minusMetric p q r ∧
      Matrix.det plusMetric = -1 ∧
      Matrix.det (minusMetric p q r) < 0 ∧
      Matrix.det (relativeMatrix p q r) > 0 ∧
      chartRoot p q r * chartRoot p q r =
        plusMetricInverse * minusMetric p q r ∧
      Matrix.det (chartRoot p q r) > 0 ∧
      Matrix.trace (chartRoot p q r) = rootDenominator p q r ∧
      ContinuousAt
        (fun point : ℝ × ℝ × ℝ =>
          chartRoot point.1 point.2.1 point.2.2)
        (p, q, r) := by
  exact ⟨plusMetric_symmetric, minusMetric_symmetric p q r,
    plusMetric_det, (minusMetric_lorentzByDet hChart).2,
    relativeMatrix_det p q r ▸ hChart.1,
    chartRoot_square_eq_metricRelative hChart,
    chartRoot_det_pos hChart, chartRoot_trace hChart,
    chartRoot_continuousAt hChart⟩

end

end P0EFTJanusLorentzPrincipalRootChart2D
end JanusFormal
