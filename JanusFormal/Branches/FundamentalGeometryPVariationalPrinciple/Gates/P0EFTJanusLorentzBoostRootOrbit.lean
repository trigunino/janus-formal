import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoDiagonalLorentzRootChart

/-!
# A coordinate off-diagonal Lorentz-boost square-root orbit

This gate gives an explicit one-parameter Lorentz orbit whose coordinate
matrices have off-diagonal entries.  In the time--space plane, let `Λ(s)` be
the standard boost and let `D = diag(2,1)`.  We construct

`X(s) = Λ(s)⁻¹ D Λ(s)` and `A(s) = X(s) X(s)`.

The boost inverse and Lorentz identities are proved, as are `X(s)^2 = A(s)`,
the relative-metric realization, non-diagonality away from zero, invariant
trace and determinant, and the actual derivative of the matrix curve.  The
derivative of the square identity is the Sylvester equation

`X X' + X' X = A'`.

The whole orbit remains Lorentz-conjugate to the diagonal seed, hence it is
still simultaneously co-diagonalizable and is not a new geometric spectral
chart.  Moreover the metric pair is reconstructed after selecting `X`; this
does not solve the root problem for independently supplied metrics.  It is not
a construction of the principal square root on the full causal-compatible
Lorentz domain, nor a proof of global branch continuation.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzBoostRootOrbit

set_option autoImplicit false

noncomputable section

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

open scoped Matrix.Norms.Elementwise

private theorem matrix_mul_curve_hasDerivAt
    {left right : ℝ → Matrix2}
    {leftDerivative rightDerivative : Matrix2} {point : ℝ}
    (hLeft : HasDerivAt left leftDerivative point)
    (hRight : HasDerivAt right rightDerivative point) :
    HasDerivAt (fun parameter => left parameter * right parameter)
      (leftDerivative * right point + left point * rightDerivative) point := by
  change HasDerivAt
    (fun parameter i j => (left parameter * right parameter) i j)
    (fun i j => (leftDerivative * right point + left point * rightDerivative) i j)
    point
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  have hSum := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hLeft i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hRight k) j))
  simpa only [Pi.mul_apply, Finset.sum_add_distrib] using hSum

/-- Minkowski metric on the boost plane. -/
def minkowskiMetric : Matrix2 := !![-1, 0; 0, 1]

/-- Standard proper Lorentz boost. -/
def lorentzBoost (rapidity : ℝ) : Matrix2 :=
  !![Real.cosh rapidity, Real.sinh rapidity;
     Real.sinh rapidity, Real.cosh rapidity]

/-- Explicit inverse boost. -/
def lorentzBoostInverse (rapidity : ℝ) : Matrix2 :=
  !![Real.cosh rapidity, -Real.sinh rapidity;
     -Real.sinh rapidity, Real.cosh rapidity]

/-- Positive, non-scalar seed root. -/
def seedRoot : Matrix2 := !![2, 0; 0, 1]

theorem seedRoot_positive_nonScalar :
    0 < seedRoot 0 0 ∧ 0 < seedRoot 1 1 ∧
      seedRoot 0 1 = 0 ∧ seedRoot 1 0 = 0 ∧
      seedRoot 0 0 ≠ seedRoot 1 1 := by
  norm_num [seedRoot]

theorem minkowskiMetric_square :
    minkowskiMetric * minkowskiMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

theorem lorentzBoostInverse_mul (rapidity : ℝ) :
    lorentzBoostInverse rapidity * lorentzBoost rapidity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoostInverse, lorentzBoost, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

theorem lorentzBoost_mul_inverse (rapidity : ℝ) :
    lorentzBoost rapidity * lorentzBoostInverse rapidity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoostInverse, lorentzBoost, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

/-- `Λ(s)` preserves the Lorentz form. -/
theorem lorentzBoost_isometry (rapidity : ℝ) :
    (lorentzBoost rapidity).transpose * minkowskiMetric *
        lorentzBoost rapidity = minkowskiMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoost, minkowskiMetric, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.transpose_apply] <;>
    nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

theorem lorentzBoost_det (rapidity : ℝ) :
    Matrix.det (lorentzBoost rapidity) = 1 := by
  rw [Matrix.det_fin_two]
  simp [lorentzBoost]
  nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

theorem lorentzBoostInverse_det (rapidity : ℝ) :
    Matrix.det (lorentzBoostInverse rapidity) = 1 := by
  rw [Matrix.det_fin_two]
  simp [lorentzBoostInverse]
  nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

/-- Non-co-diagonal root curve obtained by Lorentz similarity. -/
def rootOrbit (rapidity : ℝ) : Matrix2 :=
  lorentzBoostInverse rapidity * seedRoot * lorentzBoost rapidity

/-- The relative target is the square of the selected root along the orbit. -/
def relativeTarget (rapidity : ℝ) : Matrix2 :=
  rootOrbit rapidity * rootOrbit rapidity

theorem rootOrbit_square_eq_relativeTarget (rapidity : ℝ) :
    rootOrbit rapidity * rootOrbit rapidity = relativeTarget rapidity :=
  rfl

/-- The target is itself the Lorentz similarity orbit of `D²`. -/
theorem relativeTarget_eq_conjugated_seedSquare (rapidity : ℝ) :
    relativeTarget rapidity =
      lorentzBoostInverse rapidity * (seedRoot * seedRoot) *
        lorentzBoost rapidity := by
  unfold relativeTarget rootOrbit
  calc
    (lorentzBoostInverse rapidity * seedRoot * lorentzBoost rapidity) *
        (lorentzBoostInverse rapidity * seedRoot * lorentzBoost rapidity) =
      lorentzBoostInverse rapidity * seedRoot *
        (lorentzBoost rapidity * lorentzBoostInverse rapidity) *
          seedRoot * lorentzBoost rapidity := by noncomm_ring
    _ = lorentzBoostInverse rapidity * (seedRoot * seedRoot) *
          lorentzBoost rapidity := by
      rw [lorentzBoost_mul_inverse]
      noncomm_ring

/-- Plus metric and inverse for the explicit relative-metric realization. -/
def plusMetric : Matrix2 := minkowskiMetric

def plusMetricInverse : Matrix2 := minkowskiMetric

/-- Minus metric reconstructed after selecting `X` and setting `A = X²`; the
metric pair is not independently supplied input. -/
def minusMetric (rapidity : ℝ) : Matrix2 :=
  minkowskiMetric * relativeTarget rapidity

theorem plusMetricInverse_mul_plusMetric :
    plusMetricInverse * plusMetric = 1 :=
  minkowskiMetric_square

theorem plusMetric_symmetric : plusMetric.transpose = plusMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMetric, minkowskiMetric, Matrix.transpose_apply]

theorem plusMetric_det : Matrix.det plusMetric = -1 := by
  norm_num [plusMetric, minkowskiMetric, Matrix.det_fin_two]

theorem relativeTarget_is_metric_relative (rapidity : ℝ) :
    plusMetricInverse * minusMetric rapidity = relativeTarget rapidity := by
  unfold plusMetricInverse minusMetric
  rw [← Matrix.mul_assoc, minkowskiMetric_square, one_mul]

/-- The reconstructed minus tensor is symmetric. -/
theorem minusMetric_symmetric (rapidity : ℝ) :
    (minusMetric rapidity).transpose = minusMetric rapidity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, minusMetric, relativeTarget, rootOrbit,
      minkowskiMetric, lorentzBoostInverse, seedRoot, lorentzBoost,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- Thus `X²` is the relative matrix of the reconstructed pair by
construction. -/
theorem rootOrbit_square_eq_metricRelative (rapidity : ℝ) :
    rootOrbit rapidity * rootOrbit rapidity =
      plusMetricInverse * minusMetric rapidity := by
  rw [rootOrbit_square_eq_relativeTarget,
    relativeTarget_is_metric_relative]

theorem rootOrbit_zero_zero (rapidity : ℝ) :
    rootOrbit rapidity 0 0 =
      2 * Real.cosh rapidity ^ 2 - Real.sinh rapidity ^ 2 := by
  simp [rootOrbit, lorentzBoostInverse, seedRoot, lorentzBoost,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem rootOrbit_zero_one (rapidity : ℝ) :
    rootOrbit rapidity 0 1 =
      Real.cosh rapidity * Real.sinh rapidity := by
  simp [rootOrbit, lorentzBoostInverse, seedRoot, lorentzBoost,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem rootOrbit_one_zero (rapidity : ℝ) :
    rootOrbit rapidity 1 0 =
      -(Real.cosh rapidity * Real.sinh rapidity) := by
  simp [rootOrbit, lorentzBoostInverse, seedRoot, lorentzBoost,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem rootOrbit_one_one (rapidity : ℝ) :
    rootOrbit rapidity 1 1 =
      Real.cosh rapidity ^ 2 - 2 * Real.sinh rapidity ^ 2 := by
  simp [rootOrbit, lorentzBoostInverse, seedRoot, lorentzBoost,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Every nonzero rapidity gives an actual off-diagonal root. -/
theorem rootOrbit_nonDiagonal
    (rapidity : ℝ) (hRapidity : rapidity ≠ 0) :
    rootOrbit rapidity 0 1 ≠ 0 := by
  rw [rootOrbit_zero_one]
  exact mul_ne_zero (ne_of_gt (Real.cosh_pos rapidity))
    (Real.sinh_ne_zero.mpr hRapidity)

/-- Concrete coordinate off-diagonal witness. -/
theorem rootOrbit_one_nonDiagonal : rootOrbit 1 0 1 ≠ 0 := by
  exact rootOrbit_nonDiagonal 1 one_ne_zero

/-- Similarity preserves the two-dimensional trace. -/
theorem rootOrbit_trace (rapidity : ℝ) :
    Matrix.trace (rootOrbit rapidity) = 3 := by
  rw [Matrix.trace_fin_two, rootOrbit_zero_zero, rootOrbit_one_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

/-- Similarity preserves the determinant (and hence, with the trace, the
two-dimensional characteristic polynomial). -/
theorem rootOrbit_det (rapidity : ℝ) :
    Matrix.det (rootOrbit rapidity) = 2 := by
  rw [rootOrbit, Matrix.det_mul, Matrix.det_mul,
    lorentzBoostInverse_det, lorentzBoost_det]
  norm_num [seedRoot, Matrix.det_fin_two]

theorem relativeTarget_det (rapidity : ℝ) :
    Matrix.det (relativeTarget rapidity) = 4 := by
  rw [relativeTarget, Matrix.det_mul, rootOrbit_det]
  norm_num

/-- The symmetric minus tensor is nondegenerate and Lorentzian in dimension
two, as witnessed by its negative determinant. -/
theorem minusMetric_det (rapidity : ℝ) :
    Matrix.det (minusMetric rapidity) = -4 := by
  rw [minusMetric, Matrix.det_mul, relativeTarget_det]
  norm_num [minkowskiMetric, Matrix.det_fin_two]

/-- Entrywise derivative of the boost. -/
def lorentzBoostDerivative (rapidity : ℝ) : Matrix2 :=
  !![Real.sinh rapidity, Real.cosh rapidity;
     Real.cosh rapidity, Real.sinh rapidity]

/-- Entrywise derivative of the inverse boost. -/
def lorentzBoostInverseDerivative (rapidity : ℝ) : Matrix2 :=
  !![Real.sinh rapidity, -Real.cosh rapidity;
     -Real.cosh rapidity, Real.sinh rapidity]

/-- Infinitesimal boost generator. -/
def boostGenerator : Matrix2 := !![0, 1; 1, 0]

theorem lorentzBoost_decomposition (rapidity : ℝ) :
    lorentzBoost rapidity =
      Real.cosh rapidity • (1 : Matrix2) +
        Real.sinh rapidity • boostGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoost, boostGenerator]

theorem lorentzBoostInverse_decomposition (rapidity : ℝ) :
    lorentzBoostInverse rapidity =
      Real.cosh rapidity • (1 : Matrix2) -
        Real.sinh rapidity • boostGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoostInverse, boostGenerator]

theorem lorentzBoostDerivative_decomposition (rapidity : ℝ) :
    lorentzBoostDerivative rapidity =
      Real.sinh rapidity • (1 : Matrix2) +
        Real.cosh rapidity • boostGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoostDerivative, boostGenerator]

theorem lorentzBoostInverseDerivative_decomposition (rapidity : ℝ) :
    lorentzBoostInverseDerivative rapidity =
      Real.sinh rapidity • (1 : Matrix2) -
        Real.cosh rapidity • boostGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoostInverseDerivative, boostGenerator]

theorem lorentzBoost_hasDerivAt (rapidity : ℝ) :
    HasDerivAt lorentzBoost (lorentzBoostDerivative rapidity) rapidity := by
  have h :=
    (Real.hasDerivAt_cosh rapidity).smul_const (1 : Matrix2) |>.add
      ((Real.hasDerivAt_sinh rapidity).smul_const boostGenerator)
  have hCurve : HasDerivAt lorentzBoost
      (Real.sinh rapidity • (1 : Matrix2) +
        Real.cosh rapidity • boostGenerator) rapidity :=
    h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall lorentzBoost_decomposition)
  exact hCurve.congr_deriv
    (lorentzBoostDerivative_decomposition rapidity).symm

theorem lorentzBoostInverse_hasDerivAt (rapidity : ℝ) :
    HasDerivAt lorentzBoostInverse
      (lorentzBoostInverseDerivative rapidity) rapidity := by
  have h :=
    (Real.hasDerivAt_cosh rapidity).smul_const (1 : Matrix2) |>.sub
      ((Real.hasDerivAt_sinh rapidity).smul_const boostGenerator)
  have hCurve : HasDerivAt lorentzBoostInverse
      (Real.sinh rapidity • (1 : Matrix2) -
        Real.cosh rapidity • boostGenerator) rapidity :=
    h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall lorentzBoostInverse_decomposition)
  exact hCurve.congr_deriv
    (lorentzBoostInverseDerivative_decomposition rapidity).symm

/-- Product-rule tangent of the actual Lorentz-similarity root curve. -/
def rootOrbitDerivative (rapidity : ℝ) : Matrix2 :=
  (lorentzBoostInverseDerivative rapidity * seedRoot) *
      lorentzBoost rapidity +
    (lorentzBoostInverse rapidity * seedRoot) *
      lorentzBoostDerivative rapidity

theorem rootOrbit_hasDerivAt (rapidity : ℝ) :
    HasDerivAt rootOrbit (rootOrbitDerivative rapidity) rapidity := by
  have hSeed : HasDerivAt (fun _ : ℝ => seedRoot) 0 rapidity :=
    hasDerivAt_const rapidity seedRoot
  have hLeftRaw := matrix_mul_curve_hasDerivAt
    (lorentzBoostInverse_hasDerivAt rapidity) hSeed
  have hLeft : HasDerivAt
      (fun parameter => lorentzBoostInverse parameter * seedRoot)
      (lorentzBoostInverseDerivative rapidity * seedRoot) rapidity := by
    simpa using hLeftRaw
  have hProduct := matrix_mul_curve_hasDerivAt hLeft
    (lorentzBoost_hasDerivAt rapidity)
  refine (hProduct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro parameter
    rfl
  · rfl

/-- The Sylvester expression is the derivative of the relative target. -/
def relativeTargetDerivative (rapidity : ℝ) : Matrix2 :=
  rootOrbit rapidity * rootOrbitDerivative rapidity +
    rootOrbitDerivative rapidity * rootOrbit rapidity

theorem relativeTarget_hasDerivAt (rapidity : ℝ) :
    HasDerivAt relativeTarget
      (relativeTargetDerivative rapidity) rapidity := by
  have hProduct := matrix_mul_curve_hasDerivAt
    (rootOrbit_hasDerivAt rapidity) (rootOrbit_hasDerivAt rapidity)
  refine (hProduct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro parameter
    rfl
  · simp [relativeTargetDerivative, add_comm]

/-- Differentiating the exact square-root identity gives the genuine
Sylvester equation `X X' + X' X = A'` on the orbit. -/
theorem rootOrbit_derivative_sylvester (rapidity : ℝ) :
    rootOrbit rapidity * rootOrbitDerivative rapidity +
        rootOrbitDerivative rapidity * rootOrbit rapidity =
      relativeTargetDerivative rapidity :=
  rfl

/-- The derivative statements and Sylvester equation are packaged with the
coordinate off-diagonal witness, without claiming a new geometric spectral
class or a global Lorentzian root chart. -/
theorem lorentzBoostRootOrbit_gate :
    rootOrbit 1 0 1 ≠ 0 ∧
      (∀ rapidity : ℝ,
        HasDerivAt rootOrbit (rootOrbitDerivative rapidity) rapidity) ∧
      (∀ rapidity : ℝ,
        HasDerivAt relativeTarget
          (relativeTargetDerivative rapidity) rapidity) ∧
      (∀ rapidity : ℝ,
        rootOrbit rapidity * rootOrbit rapidity =
          plusMetricInverse * minusMetric rapidity) ∧
      (∀ rapidity : ℝ,
        (minusMetric rapidity).transpose = minusMetric rapidity) ∧
      (∀ rapidity : ℝ,
        Matrix.det (minusMetric rapidity) = -4) ∧
      (∀ rapidity : ℝ,
        rootOrbit rapidity * rootOrbitDerivative rapidity +
            rootOrbitDerivative rapidity * rootOrbit rapidity =
          relativeTargetDerivative rapidity) := by
  exact ⟨rootOrbit_one_nonDiagonal, rootOrbit_hasDerivAt,
    relativeTarget_hasDerivAt, rootOrbit_square_eq_metricRelative,
    minusMetric_symmetric, minusMetric_det, rootOrbit_derivative_sylvester⟩

end

end P0EFTJanusLorentzBoostRootOrbit
end JanusFormal
