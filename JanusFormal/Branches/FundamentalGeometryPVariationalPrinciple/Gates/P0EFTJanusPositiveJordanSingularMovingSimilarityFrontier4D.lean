import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D

/-!
# A singular moving frame regularizes one Jordan-root collision

For `t > 0`, conjugate `J₂(t²) ⊕ 1 ⊕ 1` by
`P(t) = diag(t, 1, 1, 1)`.  The target nilpotent coefficient becomes `t`,
while the divergent Hermite-root coefficient becomes the constant `1 / 2`.
The conjugated root therefore has a finite nonzero nilpotent frontier value.

The price is explicit: `P(0)` is singular and `P(t)⁻¹` is unbounded as
`t → 0⁺`.  Thus the fixed-similarity no-limit theorem is not uniform over
singular moving frames.  This example is not a classification of arbitrary
singular similarities or Jordan-type-changing paths.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanSingularMovingSimilarityFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveJordanCollisionZeroFrontier4D
open P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D

abbrev Matrix4 :=
  P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D.Matrix4

/-- The moving change of basis `diag(t, 1, 1, 1)`. -/
def singularMovingChange (parameter : Real) : Matrix4 :=
  !![parameter, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Its inverse away from zero, written on all parameters using `0⁻¹ = 0`. -/
def singularMovingInverse (parameter : Real) : Matrix4 :=
  !![parameter⁻¹, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem singularMoving_inverse_mul_change
    {parameter : Real} (hParameter : parameter ≠ 0) :
    singularMovingInverse parameter * singularMovingChange parameter = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMovingInverse, singularMovingChange, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, hParameter]

theorem singularMoving_change_mul_inverse
    {parameter : Real} (hParameter : parameter ≠ 0) :
    singularMovingChange parameter * singularMovingInverse parameter = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMovingInverse, singularMovingChange, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, hParameter]

/-- The resulting genuine similarity for every nonzero parameter. -/
def singularMovingSimilarity
    (parameter : Real) (hParameter : parameter ≠ 0) : FixedSimilarity4 where
  change := singularMovingChange parameter
  inverse := singularMovingInverse parameter
  inverse_mul_change := singularMoving_inverse_mul_change hParameter
  change_mul_inverse := singularMoving_change_mul_inverse hParameter

/-- The regularized target path, equal to the conjugate of `J₂(t²) ⊕ 1 ⊕ 1`
away from zero. -/
def singularMovingCollisionTarget (parameter : Real) : Matrix4 :=
  !![parameter ^ 2, parameter, 0, 0;
     0, parameter ^ 2, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The finite moving-frame Hermite root. -/
def singularMovingCollisionRoot (parameter : Real) : Matrix4 :=
  !![parameter, (2 : Real)⁻¹, 0, 0;
     0, parameter, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem singularMovingCollisionTarget_similarity
    {parameter : Real} (hParameter : parameter ≠ 0) :
    singularMovingCollisionTarget parameter =
      (singularMovingSimilarity parameter hParameter).conjugate
        (jordanCollisionTarget (parameter ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMovingCollisionTarget, singularMovingSimilarity,
      FixedSimilarity4.conjugate, singularMovingChange,
      singularMovingInverse, jordanCollisionTarget, Matrix.mul_apply,
      Fin.sum_univ_succ, hParameter] <;>
    field_simp [hParameter] <;> ring

theorem singularMovingCollisionRoot_similarity
    {parameter : Real} (hParameter : 0 < parameter) :
    singularMovingCollisionRoot parameter =
      (singularMovingSimilarity parameter hParameter.ne').conjugate
        (jordanCollisionRoot (parameter ^ 2)) := by
  have hSqrt : Real.sqrt (parameter ^ 2) = parameter := by
    simpa [abs_of_pos hParameter] using Real.sqrt_sq_eq_abs parameter
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMovingCollisionRoot, singularMovingSimilarity,
      FixedSimilarity4.conjugate, singularMovingChange,
      singularMovingInverse, jordanCollisionRoot, Matrix.mul_apply,
      Fin.sum_univ_succ, hParameter.ne', hSqrt] <;>
    field_simp [hParameter.ne'] <;> ring

/-- The regularized root squares exactly, including at the frontier. -/
theorem singularMovingCollisionRoot_square (parameter : Real) :
    singularMovingCollisionRoot parameter *
        singularMovingCollisionRoot parameter =
      singularMovingCollisionTarget parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMovingCollisionRoot, singularMovingCollisionTarget,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem singularMovingCollisionTarget_continuous :
    Continuous singularMovingCollisionTarget := by
  unfold singularMovingCollisionTarget
  fun_prop

theorem singularMovingCollisionRoot_continuous :
    Continuous singularMovingCollisionRoot := by
  unfold singularMovingCollisionRoot
  fun_prop

theorem singularMovingCollisionTarget_tendsto_frontier :
    Tendsto singularMovingCollisionTarget (nhdsWithin 0 (Set.Ioi 0))
      (nhds (singularMovingCollisionTarget 0)) :=
  singularMovingCollisionTarget_continuous.continuousAt.mono_left inf_le_left

theorem singularMovingCollisionRoot_tendsto_finiteFrontier :
    Tendsto singularMovingCollisionRoot (nhdsWithin 0 (Set.Ioi 0))
      (nhds (singularMovingCollisionRoot 0)) :=
  singularMovingCollisionRoot_continuous.continuousAt.mono_left inf_le_left

/-- The limiting root retains a nonzero nilpotent coefficient. -/
@[simp]
theorem singularMovingCollisionRoot_zero_nilpotentCoefficient :
    singularMovingCollisionRoot 0 0 1 = (2 : Real)⁻¹ := by
  rfl

theorem singularMovingCollisionRoot_zero_ne_zero :
    singularMovingCollisionRoot 0 ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 1) hZero
  norm_num [singularMovingCollisionRoot] at hEntry

/-- The positive conjugated branch admits the displayed continuous extension. -/
theorem singularMovingCollisionRoot_exists_continuous_extension :
    ∃ extension : Real → Matrix4,
      ContinuousAt extension 0 ∧
        ∀ (parameter : Real) (hParameter : 0 < parameter),
          extension parameter =
            (singularMovingSimilarity parameter hParameter.ne').conjugate
              (jordanCollisionRoot (parameter ^ 2)) := by
  refine ⟨singularMovingCollisionRoot,
    singularMovingCollisionRoot_continuous.continuousAt, ?_⟩
  intro parameter hParameter
  exact singularMovingCollisionRoot_similarity hParameter

/-- At zero the moving frame has no left inverse. -/
theorem singularMovingChange_zero_not_leftInvertible :
    ¬ ∃ inverse : Matrix4, inverse * singularMovingChange 0 = 1 := by
  rintro ⟨inverse, hInverse⟩
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 0) hInverse
  simpa [singularMovingChange, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply] using hEntry

@[simp]
theorem singularMovingInverse_leadingEntry (parameter : Real) :
    singularMovingInverse parameter 0 0 = parameter⁻¹ := by
  rfl

/-- The inverse frame is unbounded in its leading entry. -/
theorem singularMovingInverse_leadingEntry_tendsto_atTop :
    Tendsto (fun parameter : Real => singularMovingInverse parameter 0 0)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  simpa using tendsto_inv_nhdsGT_zero

theorem singularMovingInverse_no_finite_limit (candidate : Matrix4) :
    ¬ Tendsto singularMovingInverse (nhdsWithin 0 (Set.Ioi 0))
      (nhds candidate) := by
  intro hLimit
  have hEvaluation : Continuous (fun matrix : Matrix4 => matrix 0 0) := by
    fun_prop
  have hEntry :
      Tendsto (fun parameter : Real => singularMovingInverse parameter 0 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (candidate 0 0)) :=
    hEvaluation.continuousAt.tendsto.comp hLimit
  exact not_tendsto_atTop_of_tendsto_nhds hEntry
    singularMovingInverse_leadingEntry_tendsto_atTop

/-- A fixed normalization of the nilpotent Sylvester mode. -/
def singularMovingCollisionMode : Matrix4 :=
  jordanCollisionMode

theorem singularMovingCollisionMode_ne_zero :
    singularMovingCollisionMode ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 1) hZero
  simpa [singularMovingCollisionMode, jordanCollisionMode] using hEntry

theorem singularMovingCollisionSylvester_mode (parameter : Real) :
    sylvesterOperator (singularMovingCollisionRoot parameter)
        singularMovingCollisionMode =
      (2 * parameter) • singularMovingCollisionMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterOperator_apply, singularMovingCollisionRoot,
      singularMovingCollisionMode, jordanCollisionMode,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem singularMovingCollisionSylvesterEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real => 2 * parameter)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hContinuous : Continuous (fun parameter : Real => 2 * parameter) := by
    fun_prop
  have hAtZero :
      ContinuousAt (fun parameter : Real => 2 * parameter) 0 :=
    hContinuous.continuousAt
  rw [nhdsWithin]
  simpa using hAtZero.mono_left inf_le_left

/-- The literally transported canonical mode collapses with the singular
frame, although its fixed normalization above remains nonzero. -/
def singularMovingTransportedMode (parameter : Real) : Matrix4 :=
  parameter • jordanCollisionMode

theorem singularMovingTransportedMode_similarity
    {parameter : Real} (hParameter : parameter ≠ 0) :
    singularMovingTransportedMode parameter =
      (singularMovingSimilarity parameter hParameter).conjugate
        jordanCollisionMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMovingTransportedMode, singularMovingSimilarity,
      FixedSimilarity4.conjugate, singularMovingChange,
      singularMovingInverse, jordanCollisionMode, Matrix.mul_apply,
      Fin.sum_univ_succ, hParameter] <;>
    field_simp [hParameter] <;> ring

theorem singularMovingTransportedMode_tendsto_zero :
    Tendsto singularMovingTransportedMode (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hContinuous : Continuous singularMovingTransportedMode := by
    unfold singularMovingTransportedMode
    fun_prop
  have hAtZero : ContinuousAt singularMovingTransportedMode 0 :=
    hContinuous.continuousAt
  rw [nhdsWithin]
  simpa [singularMovingTransportedMode] using hAtZero.mono_left inf_le_left

end

end P0EFTJanusPositiveJordanSingularMovingSimilarityFrontier4D
end JanusFormal
