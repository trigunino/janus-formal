import Mathlib.LinearAlgebra.Semisimple
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
# Explicit positive Jordan-type change paths

The affine path `I + t E₀₁` has a size-two Jordan block for `t ≠ 0` and
becomes the identity at `t = 0`.  Its exact smooth square-root extension is
`I + (t / 2) E₀₁`; the Sylvester eigenvalue on `E₀₁` remains equal to `2`.

For contrast, `t (I + E₀₁)` has an exact positive-side root tending to zero,
while the same Sylvester eigenvalue collapses to zero.  These are explicit
paths only; no global classification of Jordan-type changes is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanTypeChangeFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusMatrixSquareRootFrechetSylvester

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

/-- The square-zero matrix unit `E₀₁`. -/
def jordanMode : Matrix4 :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

theorem jordanMode_square : jordanMode * jordanMode = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanMode, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `I + t E₀₁`, including its diagonalizable value at `t = 0`. -/
def typeChangeTarget (parameter : Real) : Matrix4 :=
  !![1, parameter, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The exact affine principal-root candidate `I + (t / 2) E₀₁`. -/
def typeChangeRoot (parameter : Real) : Matrix4 :=
  !![1, parameter / 2, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem typeChangeRoot_square (parameter : Real) :
    typeChangeRoot parameter * typeChangeRoot parameter =
      typeChangeTarget parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeChangeRoot, typeChangeTarget, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

@[simp]
theorem typeChangeTarget_zero : typeChangeTarget 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeChangeTarget, Matrix.one_apply]

@[simp]
theorem typeChangeRoot_zero : typeChangeRoot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeChangeRoot, Matrix.one_apply]

theorem typeChangeTarget_deviation_square (parameter : Real) :
    (typeChangeTarget parameter - 1) *
        (typeChangeTarget parameter - 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeChangeTarget, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem typeChangeTarget_deviation_ne_zero
    {parameter : Real} (hParameter : parameter ≠ 0) :
    typeChangeTarget parameter - 1 ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 1) hZero
  have : parameter = 0 := by
    simpa [typeChangeTarget, Matrix.one_apply] using hEntry
  exact hParameter this

/-- Matrix semisimplicity, hence diagonalizability over `ℝ`, expressed via
the associated endomorphism. -/
def IsSemisimpleMatrix (matrix : Matrix4) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin' matrix)

theorem typeChangeTarget_zero_semisimple :
    IsSemisimpleMatrix (typeChangeTarget 0) := by
  simp [IsSemisimpleMatrix]

/-- Away from zero the nonzero square-zero deviation rules out
diagonalizability. -/
theorem typeChangeTarget_not_semisimple
    {parameter : Real} (hParameter : parameter ≠ 0) :
    ¬ IsSemisimpleMatrix (typeChangeTarget parameter) := by
  intro hSemisimple
  have hShifted :
      Module.End.IsSemisimple
        (Matrix.toLin' (typeChangeTarget parameter - 1)) := by
    simpa [IsSemisimpleMatrix, Module.End.one_eq_id] using
      (Module.End.isSemisimple_sub_algebraMap_iff
        (f := Matrix.toLin' (typeChangeTarget parameter))
        (μ := (1 : Real))).2 hSemisimple
  have hNilpotent :
      IsNilpotent (Matrix.toLin' (typeChangeTarget parameter - 1)) := by
    refine ⟨2, ?_⟩
    rw [← Matrix.toLin'_pow]
    simp [pow_two, typeChangeTarget_deviation_square]
  have hLinearZero :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hNilpotent hShifted
  have hMatrixZero : typeChangeTarget parameter - 1 = 0 := by
    apply Matrix.toLin'.injective
    simpa using hLinearZero
  exact typeChangeTarget_deviation_ne_zero hParameter hMatrixZero

theorem typeChangeTarget_contDiff :
    ContDiff Real ⊤ typeChangeTarget := by
  have hFormula :
      typeChangeTarget = fun parameter : Real =>
        (1 : Matrix4) + parameter • jordanMode := by
    funext parameter
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [typeChangeTarget, jordanMode, Matrix.one_apply]
  rw [hFormula]
  fun_prop

theorem typeChangeRoot_contDiff :
    ContDiff Real ⊤ typeChangeRoot := by
  have hFormula :
      typeChangeRoot = fun parameter : Real =>
        (1 : Matrix4) + (parameter / 2) • jordanMode := by
    funext parameter
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [typeChangeRoot, jordanMode, Matrix.one_apply]
  rw [hFormula]
  fun_prop

/-- The nilpotent mode remains uniformly Sylvester-regular across the type
change: its eigenvalue is exactly `2`. -/
theorem typeChangeSylvester_mode (parameter : Real) :
    sylvesterOperator (typeChangeRoot parameter) jordanMode =
      (2 : Real) • jordanMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterOperator_apply, typeChangeRoot, jordanMode,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The contrasting target `t (I + E₀₁)`. -/
def zeroFrontierTarget (parameter : Real) : Matrix4 :=
  !![parameter, parameter, 0, 0;
     0, parameter, 0, 0;
     0, 0, parameter, 0;
     0, 0, 0, parameter]

/-- Its exact positive-side square root
`sqrt t (I + E₀₁ / 2)`. -/
def zeroFrontierRoot (parameter : Real) : Matrix4 :=
  !![Real.sqrt parameter, Real.sqrt parameter / 2, 0, 0;
     0, Real.sqrt parameter, 0, 0;
     0, 0, Real.sqrt parameter, 0;
     0, 0, 0, Real.sqrt parameter]

theorem zeroFrontierRoot_square
    {parameter : Real} (hParameter : 0 ≤ parameter) :
    zeroFrontierRoot parameter * zeroFrontierRoot parameter =
      zeroFrontierTarget parameter := by
  have hSquare := Real.sq_sqrt hParameter
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroFrontierRoot, zeroFrontierTarget, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> nlinarith

@[simp]
theorem zeroFrontierRoot_zero : zeroFrontierRoot 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroFrontierRoot]

theorem zeroFrontierRoot_continuous : Continuous zeroFrontierRoot := by
  unfold zeroFrontierRoot
  fun_prop

theorem zeroFrontierRoot_tendsto_zero :
    Tendsto zeroFrontierRoot (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hAtZero :
      Tendsto zeroFrontierRoot (nhdsWithin 0 (Set.Ioi 0))
        (nhds (zeroFrontierRoot 0)) :=
    zeroFrontierRoot_continuous.continuousAt.mono_left inf_le_left
  simpa using hAtZero

theorem zeroFrontierSylvester_mode (parameter : Real) :
    sylvesterOperator (zeroFrontierRoot parameter) jordanMode =
      (2 * Real.sqrt parameter) • jordanMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterOperator_apply, zeroFrontierRoot, jordanMode,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem zeroFrontierSylvesterEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real => 2 * Real.sqrt parameter)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hSqrt :
      Tendsto (fun parameter : Real => Real.sqrt parameter)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hContinuousAt :
        ContinuousAt (fun parameter : Real => Real.sqrt parameter) 0 :=
      Real.continuous_sqrt.continuousAt
    have hRestricted := hContinuousAt.mono_left
      (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
    simpa using hRestricted
  simpa using hSqrt.const_mul 2

end

end P0EFTJanusPositiveJordanTypeChangeFrontier4D
end JanusFormal
