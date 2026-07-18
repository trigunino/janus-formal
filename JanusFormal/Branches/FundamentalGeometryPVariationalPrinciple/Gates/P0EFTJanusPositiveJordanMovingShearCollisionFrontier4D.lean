import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D

/-!
# A nonconstant moving-similarity Jordan collision

The polynomial shear `P(t) = I + t E₂₀` has the exact inverse
`P(t)⁻¹ = I - t E₂₀`.  Conjugating `J₂(t) ⊕ 1 ⊕ 1` by this genuinely moving
similarity gives an exact positive root for `t > 0`.  The target converges at
zero, while the root keeps the divergent `(0,1)` Hermite coefficient and has
no finite continuation.  The transported Sylvester mode is
`E₀₁ + t E₂₁`, with collapsing eigenvalue `2 * sqrt t`.

This gate does not cover similarities that become singular or unbounded,
arbitrary non-polynomial moving frames without controlled inverses, or paths
that change Jordan type.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanMovingShearCollisionFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveJordanCollisionZeroFrontier4D
open P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D

abbrev Matrix4 :=
  P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D.Matrix4

/-- The square-zero generator `E₂₀`. -/
def movingShearGenerator : Matrix4 :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0]

def movingShearChange (parameter : Real) : Matrix4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     parameter, 0, 1, 0;
     0, 0, 0, 1]

def movingShearInverse (parameter : Real) : Matrix4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     -parameter, 0, 1, 0;
     0, 0, 0, 1]

theorem movingShearGenerator_square :
    movingShearGenerator * movingShearGenerator = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [movingShearGenerator]

theorem movingShear_inverse_mul_change (parameter : Real) :
    movingShearInverse parameter * movingShearChange parameter = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [movingShearInverse, movingShearChange, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem movingShear_change_mul_inverse (parameter : Real) :
    movingShearChange parameter * movingShearInverse parameter = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [movingShearInverse, movingShearChange, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply] <;> ring

/-- The explicit moving similarity at each parameter. -/
def movingShearSimilarity (parameter : Real) : FixedSimilarity4 where
  change := movingShearChange parameter
  inverse := movingShearInverse parameter
  inverse_mul_change := movingShear_inverse_mul_change parameter
  change_mul_inverse := movingShear_change_mul_inverse parameter

def movingShearCollisionTarget (parameter : Real) : Matrix4 :=
  similarJordanCollisionTarget (movingShearSimilarity parameter) parameter

def movingShearCollisionRoot (parameter : Real) : Matrix4 :=
  similarJordanCollisionRoot (movingShearSimilarity parameter) parameter

def movingShearCollisionMode (parameter : Real) : Matrix4 :=
  similarJordanCollisionMode (movingShearSimilarity parameter)

theorem movingShearCollisionRoot_square
    {parameter : Real} (hParameter : 0 < parameter) :
    movingShearCollisionRoot parameter *
        movingShearCollisionRoot parameter =
      movingShearCollisionTarget parameter :=
  similarJordanCollisionRoot_square
    (movingShearSimilarity parameter) hParameter

/-- This entry proves that the conjugated target path is genuinely moving
outside the original block-diagonal family. -/
theorem movingShearCollisionTarget_lowerOffDiagonal
    (parameter : Real) :
    movingShearCollisionTarget parameter 2 1 = parameter := by
  simp [movingShearCollisionTarget, similarJordanCollisionTarget,
    movingShearSimilarity, FixedSimilarity4.conjugate,
    movingShearChange, movingShearInverse, movingShearGenerator,
    jordanCollisionTarget, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply]

theorem movingShearCollisionTarget_nonconstant :
    movingShearCollisionTarget 0 ≠ movingShearCollisionTarget 1 := by
  intro hEqual
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 2 1) hEqual
  simpa [movingShearCollisionTarget_lowerOffDiagonal] using hEntry

@[simp]
theorem movingShearCollisionTarget_zero :
    movingShearCollisionTarget 0 = jordanCollisionTarget 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [movingShearCollisionTarget, similarJordanCollisionTarget,
      movingShearSimilarity, FixedSimilarity4.conjugate,
      movingShearChange, movingShearInverse, jordanCollisionTarget,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem movingShearCollisionTarget_tendsto_zeroFrontier :
    Tendsto movingShearCollisionTarget (nhdsWithin 0 (Set.Ioi 0))
      (nhds (jordanCollisionTarget 0)) := by
  have hContinuous : Continuous movingShearCollisionTarget := by
    unfold movingShearCollisionTarget similarJordanCollisionTarget
      FixedSimilarity4.conjugate movingShearSimilarity
      movingShearChange movingShearInverse jordanCollisionTarget
    fun_prop
  have hAtZero :
      Tendsto movingShearCollisionTarget (nhdsWithin 0 (Set.Ioi 0))
        (nhds (movingShearCollisionTarget 0)) :=
    hContinuous.continuousAt.mono_left inf_le_left
  simpa only [movingShearCollisionTarget_zero] using hAtZero

/-- The moving shear does not hide the divergent Hermite coefficient. -/
@[simp]
theorem movingShearCollisionRoot_nilpotentCoefficient
    (parameter : Real) :
    movingShearCollisionRoot parameter 0 1 =
      (2 * Real.sqrt parameter)⁻¹ := by
  simp [movingShearCollisionRoot, similarJordanCollisionRoot,
    movingShearSimilarity, FixedSimilarity4.conjugate,
    movingShearChange, movingShearInverse, movingShearGenerator,
    jordanCollisionRoot, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply]

theorem movingShearCollisionRoot_nilpotentCoefficient_tendsto_atTop :
    Tendsto (fun parameter : Real => movingShearCollisionRoot parameter 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  simpa using jordanCollisionRoot_nilpotentCoefficient_tendsto_atTop

theorem movingShearCollisionMode_formula (parameter : Real) :
    movingShearCollisionMode parameter =
      jordanCollisionMode + parameter •
        !![0, 0, 0, 0;
           0, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [movingShearCollisionMode, similarJordanCollisionMode,
      movingShearSimilarity, FixedSimilarity4.conjugate,
      movingShearChange, movingShearInverse, movingShearGenerator,
      jordanCollisionMode, Matrix.one_apply] <;> ring

theorem movingShearCollisionMode_ne_zero (parameter : Real) :
    movingShearCollisionMode parameter ≠ 0 :=
  similarJordanCollisionMode_ne_zero (movingShearSimilarity parameter)

@[simp]
theorem movingShearCollisionMode_zero :
    movingShearCollisionMode 0 = jordanCollisionMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [movingShearCollisionMode, similarJordanCollisionMode,
      movingShearSimilarity, FixedSimilarity4.conjugate,
      movingShearChange, movingShearInverse, jordanCollisionMode,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem movingShearCollisionMode_tendsto_canonical :
    Tendsto movingShearCollisionMode (nhdsWithin 0 (Set.Ioi 0))
      (nhds jordanCollisionMode) := by
  have hContinuous : Continuous movingShearCollisionMode := by
    unfold movingShearCollisionMode similarJordanCollisionMode
      movingShearSimilarity FixedSimilarity4.conjugate movingShearChange
      movingShearInverse
    fun_prop
  have hAtZero :
      Tendsto movingShearCollisionMode (nhdsWithin 0 (Set.Ioi 0))
        (nhds (movingShearCollisionMode 0)) :=
    hContinuous.continuousAt.mono_left inf_le_left
  simpa only [movingShearCollisionMode_zero] using hAtZero

theorem movingShearCollisionSylvester_mode (parameter : Real) :
    sylvesterOperator (movingShearCollisionRoot parameter)
        (movingShearCollisionMode parameter) =
      (2 * Real.sqrt parameter) • movingShearCollisionMode parameter :=
  similarJordanCollisionSylvester_mode
    (movingShearSimilarity parameter) parameter

theorem movingShearCollisionSylvesterEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real => 2 * Real.sqrt parameter)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  jordanCollisionSylvesterEigenvalue_tendsto_zero

theorem movingShearCollisionRoot_no_finite_limit (candidate : Matrix4) :
    ¬ Tendsto movingShearCollisionRoot (nhdsWithin 0 (Set.Ioi 0))
      (nhds candidate) := by
  intro hLimit
  have hEvaluation : Continuous (fun matrix : Matrix4 => matrix 0 1) := by
    fun_prop
  have hCoefficient :
      Tendsto (fun parameter => movingShearCollisionRoot parameter 0 1)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (candidate 0 1)) :=
    hEvaluation.continuousAt.tendsto.comp hLimit
  exact not_tendsto_atTop_of_tendsto_nhds hCoefficient
    movingShearCollisionRoot_nilpotentCoefficient_tendsto_atTop

theorem movingShearCollisionRoot_no_continuous_extension :
    ¬ ∃ extension : Real → Matrix4,
        ContinuousAt extension 0 ∧
          ∀ parameter, 0 < parameter →
            extension parameter = movingShearCollisionRoot parameter := by
  rintro ⟨extension, hContinuous, hAgreement⟩
  have hRestricted :
      Tendsto extension (nhdsWithin 0 (Set.Ioi 0))
        (nhds (extension 0)) :=
    hContinuous.mono_left inf_le_left
  have hEventually :
      extension =ᶠ[nhdsWithin 0 (Set.Ioi 0)] movingShearCollisionRoot := by
    filter_upwards [self_mem_nhdsWithin] with parameter hParameter
    exact hAgreement parameter hParameter
  exact movingShearCollisionRoot_no_finite_limit (extension 0)
    (hRestricted.congr' hEventually)

end

end P0EFTJanusPositiveJordanMovingShearCollisionFrontier4D
end JanusFormal
