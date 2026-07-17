import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
# A positive Jordan collision at the zero frontier

The family `J₂(t) ⊕ 1 ⊕ 1` has an exact positive Hermite root for `t > 0`.
Its nilpotent coefficient is `1 / (2 * sqrt t)`, so the root has no finite
continuation when the double positive eigenvalue collides with zero.  On the
same family, a Sylvester mode has eigenvalue `2 * sqrt t` and collapses at the
frontier.  This is the explicit Jordan/`0 / 0` residual case.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanCollisionZeroFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open Filter

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

/-- `J₂(t) ⊕ 1 ⊕ 1`. -/
def jordanCollisionTarget (parameter : Real) : Matrix4 :=
  !![parameter, 1, 0, 0;
     0, parameter, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The Hermite square root of `J₂(t) ⊕ 1 ⊕ 1` for `t > 0`. -/
def jordanCollisionRoot (parameter : Real) : Matrix4 :=
  !![Real.sqrt parameter, (2 * Real.sqrt parameter)⁻¹, 0, 0;
     0, Real.sqrt parameter, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem jordanCollisionRoot_square
    {parameter : Real} (hParameter : 0 < parameter) :
    jordanCollisionRoot parameter * jordanCollisionRoot parameter =
      jordanCollisionTarget parameter := by
  have hSqrt : Real.sqrt parameter ≠ 0 :=
    (Real.sqrt_pos.2 hParameter).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanCollisionRoot, jordanCollisionTarget, Matrix.mul_apply,
      Fin.sum_univ_succ, hSqrt] <;>
    try { field_simp [hSqrt] <;> ring }
  all_goals simpa [pow_two] using Real.sq_sqrt hParameter.le

@[simp]
theorem jordanCollisionRoot_nilpotentCoefficient (parameter : Real) :
    jordanCollisionRoot parameter 0 1 =
      (2 * Real.sqrt parameter)⁻¹ := by
  rfl

/-- The Hermite nilpotent coefficient diverges at the positive zero frontier. -/
theorem jordanCollisionRoot_nilpotentCoefficient_tendsto_atTop :
    Tendsto (fun parameter : Real => jordanCollisionRoot parameter 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hDivergence :
      Tendsto (fun parameter : Real => (2 : Real)⁻¹ * Real.sqrt parameter⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop
      (by norm_num)
  refine hDivergence.congr' ?_
  filter_upwards with parameter
  simp [jordanCollisionRoot, Real.sqrt_inv]
  ring

private theorem matrixEntry_norm_le
    (matrix : Matrix4) (row column : Fin 4) :
    ‖matrix row column‖ ≤ ‖matrix‖ := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  have hColumn :
      ‖matrix row column‖ ^ 2 ≤ ∑ j, ‖matrix row j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖matrix row j‖)
      (Finset.mem_univ column)
  have hRow :
      (∑ j, ‖matrix row j‖ ^ 2) ≤ ∑ i, ∑ j, ‖matrix i j‖ ^ 2 :=
    Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖matrix i j‖)
      (Finset.mem_univ row)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.rpow_two] using
    Real.sqrt_le_sqrt (hColumn.trans hRow)

/-- The entire Hermite root diverges in Frobenius norm. -/
theorem jordanCollisionRoot_norm_tendsto_atTop :
    Tendsto (fun parameter : Real => ‖jordanCollisionRoot parameter‖)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  refine tendsto_atTop_mono' _ (Eventually.of_forall fun parameter => ?_)
    jordanCollisionRoot_nilpotentCoefficient_tendsto_atTop
  have hEntry := matrixEntry_norm_le (jordanCollisionRoot parameter) 0 1
  simpa [jordanCollisionRoot, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg parameter)]
    using hEntry

/-- The target itself has a perfectly finite zero-frontier limit. -/
theorem jordanCollisionTarget_tendsto_zeroFrontier :
    Tendsto jordanCollisionTarget (nhdsWithin 0 (Set.Ioi 0))
      (nhds (jordanCollisionTarget 0)) := by
  have hContinuous : Continuous jordanCollisionTarget := by
    unfold jordanCollisionTarget
    fun_prop
  rw [nhdsWithin]
  exact hContinuous.continuousAt.mono_left
    (show nhds 0 ⊓ principal (Set.Ioi 0) ≤ nhds 0 from inf_le_left)

/-- In contrast with the target, this Hermite root cannot tend to any finite
matrix at the zero frontier. -/
theorem jordanCollisionRoot_no_finite_limit (candidate : Matrix4) :
    ¬ Tendsto jordanCollisionRoot (nhdsWithin 0 (Set.Ioi 0))
      (nhds candidate) := by
  intro hLimit
  have hNorm :
      Tendsto (fun parameter : Real => ‖jordanCollisionRoot parameter‖)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖candidate‖) := by
    simpa using hLimit.norm
  exact not_tendsto_atTop_of_tendsto_nhds hNorm
    jordanCollisionRoot_norm_tendsto_atTop

/-- Therefore no branch agreeing with the positive Hermite root can extend
continuously through `t = 0`. -/
theorem jordanCollisionRoot_no_continuous_extension :
    ¬ ∃ extension : Real → Matrix4,
        ContinuousAt extension 0 ∧
          ∀ parameter, 0 < parameter →
            extension parameter = jordanCollisionRoot parameter := by
  rintro ⟨extension, hContinuous, hAgreement⟩
  have hRestricted :
      Tendsto extension (nhdsWithin 0 (Set.Ioi 0))
        (nhds (extension 0)) :=
    hContinuous.mono_left inf_le_left
  have hEventually :
      extension =ᶠ[nhdsWithin 0 (Set.Ioi 0)] jordanCollisionRoot := by
    filter_upwards [self_mem_nhdsWithin] with parameter hParameter
    exact hAgreement parameter hParameter
  exact jordanCollisionRoot_no_finite_limit (extension 0)
    (hRestricted.congr' hEventually)

/-- The matrix unit carrying the collapsing Jordan/Sylvester mode. -/
def jordanCollisionMode : Matrix4 :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

theorem jordanCollisionSylvester_mode
    (parameter : Real) :
    sylvesterOperator (jordanCollisionRoot parameter) jordanCollisionMode =
      (2 * Real.sqrt parameter) • jordanCollisionMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterOperator_apply, jordanCollisionRoot, jordanCollisionMode,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The corresponding Sylvester eigenvalue collapses to zero. -/
theorem jordanCollisionSylvesterEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real => 2 * Real.sqrt parameter)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hSqrt :
      Tendsto (fun parameter : Real => Real.sqrt parameter)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hAtZero :
        Tendsto (fun parameter : Real => Real.sqrt parameter)
          (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt
    rw [nhdsWithin]
    simpa using hAtZero.mono_left
      (show nhds 0 ⊓ principal (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa using hSqrt.const_mul 2

end

end P0EFTJanusPositiveJordanCollisionZeroFrontier4D
end JanusFormal
