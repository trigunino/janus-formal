import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzPrincipalRootChart2D
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Sylvester invertibility on the two-dimensional Lorentz root chart

For the explicit root `X` constructed by
`P0EFTJanusLorentzPrincipalRootChart2D`, this gate studies the linear
Sylvester operator

`L_X(Y) = X Y + Y X`.

An explicit coordinate inverse is proved for every real matrix
`X = [[a,b],[c,a]]` with `a != 0` and `det X = a^2 - b*c != 0`.  The chart
hypotheses imply both conditions because the selected root has positive trace
and positive determinant.  Consequently every target variation has a unique
Sylvester preimage.  This is a local real two-dimensional chart result; it is
not a four-dimensional or global principal-root theorem.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzRootSylvesterChart2D

set_option autoImplicit false

noncomputable section

open P0EFTJanusLorentzPrincipalRootChart2D

abbrev Matrix2 := P0EFTJanusLorentzPrincipalRootChart2D.Matrix2

/-- The equal-diagonal coordinate shape of every root in the 2D chart. -/
def equalDiagonalMatrix (a b c : ℝ) : Matrix2 := !![a, b; c, a]

/-- The Sylvester operator `Y |-> X*Y + Y*X`, bundled linearly. -/
def sylvesterLinear (X : Matrix2) : Matrix2 →ₗ[ℝ] Matrix2 :=
  mulLeftLinearMap (Fin 2) ℝ X +
    mulRightLinearMap (Fin 2) ℝ X

@[simp]
theorem sylvesterLinear_apply (X Y : Matrix2) :
    sylvesterLinear X Y = X * Y + Y * X :=
  rfl

/-- Trace coordinate of the explicit inverse. -/
def inverseSumCoordinate (a b c : ℝ) (H : Matrix2) : ℝ :=
  (a * (H 0 0 + H 1 1) - b * H 1 0 - c * H 0 1) /
    (2 * (a ^ 2 - b * c))

/-- Diagonal-difference coordinate of the explicit inverse. -/
def inverseDifferenceCoordinate (a : ℝ) (H : Matrix2) : ℝ :=
  (H 0 0 - H 1 1) / (2 * a)

/-- Explicit inverse candidate for the equal-diagonal Sylvester operator. -/
def equalDiagonalSylvesterInverse (a b c : ℝ) (H : Matrix2) : Matrix2 :=
  let s := inverseSumCoordinate a b c H
  let delta := inverseDifferenceCoordinate a H
  !![(s + delta) / 2, (H 0 1 - b * s) / (2 * a);
     (H 1 0 - c * s) / (2 * a), (s - delta) / 2]

/-- The displayed formula is a right inverse of the Sylvester operator. -/
theorem equalDiagonalSylvesterInverse_right
    {a b c : ℝ} (ha : a ≠ 0) (hdet : a ^ 2 - b * c ≠ 0)
    (H : Matrix2) :
    sylvesterLinear (equalDiagonalMatrix a b c)
        (equalDiagonalSylvesterInverse a b c H) = H := by
  have hdet' : a ^ 2 - c * b ≠ 0 := by
    simpa [mul_comm] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterLinear, equalDiagonalMatrix,
      equalDiagonalSylvesterInverse, inverseSumCoordinate,
      inverseDifferenceCoordinate]
  all_goals
    field_simp [ha, hdet, hdet']; ring

/-- The equal-diagonal Sylvester map is surjective, with the displayed
coordinate formula furnishing a preimage. -/
theorem equalDiagonal_sylvester_surjective
    {a b c : ℝ} (ha : a ≠ 0) (hdet : a ^ 2 - b * c ≠ 0) :
    Function.Surjective (sylvesterLinear (equalDiagonalMatrix a b c)) := by
  intro H
  exact ⟨equalDiagonalSylvesterInverse a b c H,
    equalDiagonalSylvesterInverse_right ha hdet H⟩

/-- The equal-diagonal Sylvester map is injective under the sharp coordinate
nonvanishing conditions used by the inverse formula. -/
theorem equalDiagonal_sylvester_injective
    {a b c : ℝ} (ha : a ≠ 0) (hdet : a ^ 2 - b * c ≠ 0) :
    Function.Injective (sylvesterLinear (equalDiagonalMatrix a b c)) :=
  LinearMap.injective_iff_surjective.mpr
    (equalDiagonal_sylvester_surjective ha hdet)

/-- The displayed formula is also a left inverse. -/
theorem equalDiagonalSylvesterInverse_left
    {a b c : ℝ} (ha : a ≠ 0) (hdet : a ^ 2 - b * c ≠ 0)
    (Y : Matrix2) :
    equalDiagonalSylvesterInverse a b c
        (sylvesterLinear (equalDiagonalMatrix a b c) Y) = Y := by
  apply equalDiagonal_sylvester_injective ha hdet
  exact equalDiagonalSylvesterInverse_right ha hdet
    (sylvesterLinear (equalDiagonalMatrix a b c) Y)

/-- Coordinate-level bijectivity certificate. -/
theorem equalDiagonal_sylvester_bijective
    {a b c : ℝ} (ha : a ≠ 0) (hdet : a ^ 2 - b * c ≠ 0) :
    Function.Bijective (sylvesterLinear (equalDiagonalMatrix a b c)) :=
  ⟨equalDiagonal_sylvester_injective ha hdet,
    equalDiagonal_sylvester_surjective ha hdet⟩

/-- Common diagonal entry of the selected chart root. -/
def chartDiagonal (p q r : ℝ) : ℝ :=
  (q + Real.sqrt (relativeDiscriminant p q r)) /
    rootDenominator p q r

/-- Upper-right entry of the selected chart root. -/
def chartUpper (p q r : ℝ) : ℝ := r / rootDenominator p q r

/-- Lower-left entry of the selected chart root. -/
def chartLower (p q r : ℝ) : ℝ := p / rootDenominator p q r

theorem chartRoot_eq_equalDiagonal (p q r : ℝ) :
    chartRoot p q r =
      equalDiagonalMatrix (chartDiagonal p q r)
        (chartUpper p q r) (chartLower p q r) := by
  rfl

/-- Positive root trace forces its common diagonal entry to be positive. -/
theorem chartDiagonal_pos
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    0 < chartDiagonal p q r := by
  have hTrace : 0 < Matrix.trace (chartRoot p q r) := by
    rw [chartRoot_trace hChart]
    exact rootDenominator_pos hChart
  have hCoordinate : Matrix.trace (chartRoot p q r) =
      2 * chartDiagonal p q r := by
    rw [Matrix.trace_fin_two]
    norm_num [chartRoot, chartDiagonal]
    ring
  rw [hCoordinate] at hTrace
  linarith

/-- Positive determinant becomes the nonzero denominator in the coordinate
inverse formula. -/
theorem chartCoordinateDet_pos
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    0 < chartDiagonal p q r ^ 2 -
      chartUpper p q r * chartLower p q r := by
  have hDet := chartRoot_det_pos hChart
  rw [chartRoot_eq_equalDiagonal, Matrix.det_fin_two] at hDet
  simpa [equalDiagonalMatrix, pow_two] using hDet

/-- Explicit inverse specialized to the Lorentz square-root chart. -/
def chartSylvesterInverse (p q r : ℝ) (H : Matrix2) : Matrix2 :=
  equalDiagonalSylvesterInverse (chartDiagonal p q r)
    (chartUpper p q r) (chartLower p q r) H

theorem chartSylvesterInverse_right
    {p q r : ℝ} (hChart : RootChartCondition p q r) (H : Matrix2) :
    sylvesterLinear (chartRoot p q r)
        (chartSylvesterInverse p q r H) = H := by
  rw [chartRoot_eq_equalDiagonal]
  exact equalDiagonalSylvesterInverse_right
    (ne_of_gt (chartDiagonal_pos hChart))
    (ne_of_gt (chartCoordinateDet_pos hChart)) H

theorem chart_sylvester_surjective
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Function.Surjective (sylvesterLinear (chartRoot p q r)) := by
  intro H
  exact ⟨chartSylvesterInverse p q r H,
    chartSylvesterInverse_right hChart H⟩

theorem chart_sylvester_injective
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Function.Injective (sylvesterLinear (chartRoot p q r)) :=
  LinearMap.injective_iff_surjective.mpr
    (chart_sylvester_surjective hChart)

theorem chart_sylvester_bijective
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Function.Bijective (sylvesterLinear (chartRoot p q r)) :=
  ⟨chart_sylvester_injective hChart, chart_sylvester_surjective hChart⟩

theorem chartSylvesterInverse_left
    {p q r : ℝ} (hChart : RootChartCondition p q r) (Y : Matrix2) :
    chartSylvesterInverse p q r
        (sylvesterLinear (chartRoot p q r) Y) = Y := by
  apply chart_sylvester_injective hChart
  exact chartSylvesterInverse_right hChart
    (sylvesterLinear (chartRoot p q r) Y)

/-- Every target variation has exactly one Sylvester preimage. -/
theorem existsUnique_chart_sylvester_solution
    {p q r : ℝ} (hChart : RootChartCondition p q r) (H : Matrix2) :
    ∃! Y : Matrix2,
      chartRoot p q r * Y + Y * chartRoot p q r = H := by
  refine ⟨chartSylvesterInverse p q r H, ?_, ?_⟩
  · exact chartSylvesterInverse_right hChart H
  · intro Y hY
    apply chart_sylvester_injective hChart
    calc
      sylvesterLinear (chartRoot p q r) Y = H := hY
      _ = sylvesterLinear (chartRoot p q r)
          (chartSylvesterInverse p q r H) :=
        (chartSylvesterInverse_right hChart H).symm

/-- Entrywise derivative notion for a matrix-valued real curve. -/
def MatrixCurveHasDerivAt
    (F : ℝ → Matrix2) (Fdot : Matrix2) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s ↦ F s i j) (Fdot i j) t

/-- Matrix multiplication obeys the product rule entrywise. -/
theorem matrixCurveHasDerivAt_mul
    {F G : ℝ → Matrix2} {Fdot Gdot : Matrix2} {t : ℝ}
    (hF : MatrixCurveHasDerivAt F Fdot t)
    (hG : MatrixCurveHasDerivAt G Gdot t) :
    MatrixCurveHasDerivAt (fun s ↦ F s * G s)
      (F t * Gdot + Fdot * G t) t := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]
  have hDerivative : HasDerivAt
      (fun s ↦ F s i 0 * G s 0 j + F s i 1 * G s 1 j)
      ((Fdot i 0 * G t 0 j + F t i 0 * Gdot 0 j) +
        (Fdot i 1 * G t 1 j + F t i 1 * Gdot 1 j)) t :=
    ((hF i 0).mul (hG 0 j)).add ((hF i 1).mul (hG 1 j))
  exact HasDerivAt.congr_deriv hDerivative (by ring)

/-- Differentiating `X^2 = A` gives the Sylvester equation
`X*Xdot + Xdot*X = Adot`. -/
theorem squareCurve_derivative_sylvester
    {X A : ℝ → Matrix2} {Xdot Adot : Matrix2} {t : ℝ}
    (hX : MatrixCurveHasDerivAt X Xdot t)
    (hA : MatrixCurveHasDerivAt A Adot t)
    (hSquare : ∀ s, X s * X s = A s) :
    sylvesterLinear (X t) Xdot = Adot := by
  have hProduct := matrixCurveHasDerivAt_mul hX hX
  ext i j
  have hProductEntry := hProduct i j
  have hFunctions : (fun s ↦ (X s * X s) i j) =
      (fun s ↦ A s i j) := by
    funext s
    exact congrFun (congrFun (hSquare s) i) j
  rw [hFunctions] at hProductEntry
  exact hProductEntry.unique (hA i j)

/-- At a point of the explicit chart, any differentiable square-root curve has
the unique derivative supplied by the coordinate Sylvester inverse. -/
theorem chartRoot_directionalDerivative_eq_sylvesterInverse
    {p q r t : ℝ} {X A : ℝ → Matrix2}
    {Xdot Adot : Matrix2}
    (hChart : RootChartCondition p q r)
    (hAt : X t = chartRoot p q r)
    (hX : MatrixCurveHasDerivAt X Xdot t)
    (hA : MatrixCurveHasDerivAt A Adot t)
    (hSquare : ∀ s, X s * X s = A s) :
    Xdot = chartSylvesterInverse p q r Adot := by
  have hSylvester := squareCurve_derivative_sylvester hX hA hSquare
  rw [hAt] at hSylvester
  apply chart_sylvester_injective hChart
  calc
    sylvesterLinear (chartRoot p q r) Xdot = Adot := hSylvester
    _ = sylvesterLinear (chartRoot p q r)
        (chartSylvesterInverse p q r Adot) :=
      (chartSylvesterInverse_right hChart Adot).symm

/-- The actual explicit chart root satisfies the same directional-variation
formula along every differentiable parameter curve that stays in the chart. -/
theorem explicitChartRoot_directionalDerivative_eq_sylvesterInverse
    (parameters : ℝ → ℝ × ℝ × ℝ) {t : ℝ}
    {Xdot Adot : Matrix2}
    (hChart : ∀ s, RootChartCondition
      (parameters s).1 (parameters s).2.1 (parameters s).2.2)
    (hRoot : MatrixCurveHasDerivAt
      (fun s ↦ chartRoot (parameters s).1
        (parameters s).2.1 (parameters s).2.2) Xdot t)
    (hRelative : MatrixCurveHasDerivAt
      (fun s ↦ relativeMatrix (parameters s).1
        (parameters s).2.1 (parameters s).2.2) Adot t) :
    Xdot = chartSylvesterInverse (parameters t).1
      (parameters t).2.1 (parameters t).2.2 Adot := by
  apply chartRoot_directionalDerivative_eq_sylvesterInverse
    (p := (parameters t).1) (q := (parameters t).2.1)
    (r := (parameters t).2.2) (t := t)
    (X := fun s ↦ chartRoot (parameters s).1
      (parameters s).2.1 (parameters s).2.2)
    (A := fun s ↦ relativeMatrix (parameters s).1
      (parameters s).2.1 (parameters s).2.2)
    (hChart t) rfl hRoot hRelative
  intro s
  exact chartRoot_square (hChart s)

/-- Combined local 2D certificate. -/
theorem lorentzRootSylvesterChart2D_gate
    {p q r : ℝ} (hChart : RootChartCondition p q r) :
    Function.Bijective (sylvesterLinear (chartRoot p q r)) ∧
      (∀ H : Matrix2, ∃! Y : Matrix2,
        chartRoot p q r * Y + Y * chartRoot p q r = H) ∧
      (∀ H : Matrix2,
        sylvesterLinear (chartRoot p q r)
          (chartSylvesterInverse p q r H) = H) := by
  exact ⟨chart_sylvester_bijective hChart,
    existsUnique_chart_sylvester_solution hChart,
    chartSylvesterInverse_right hChart⟩

end

end P0EFTJanusLorentzRootSylvesterChart2D
end JanusFormal
