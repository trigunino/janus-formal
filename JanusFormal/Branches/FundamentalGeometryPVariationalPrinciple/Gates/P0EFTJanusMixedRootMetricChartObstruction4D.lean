import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalSylvesterInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # A mixed-sign root obstructs a metric-direction root chart

This is a finite-dimensional matrix obstruction. It does not assert a global
realization in the Candidate-A field space or impossibility of T03 on a
specified regular root stratum.
-/

namespace JanusFormal
namespace P0EFTJanusMixedRootMetricChartObstruction4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

/-- Both the signature matrix η and the selected mixed-sign root B. -/
def mixedRoot : Matrix4 :=
  Matrix.diagonal (fun i : Fin 4 => if i = 0 then -1 else 1)

/-- An η-selfadjoint relative-metric direction with A₀₁=-1 and A₁₀=1. -/
def mixedMetricDirection : Matrix4 :=
  Matrix.single 0 1 (-1) + Matrix.single 1 0 1

theorem mixedRoot_square : mixedRoot * mixedRoot = 1 := by
  unfold mixedRoot
  rw [Matrix.diagonal_mul_diagonal]
  have hSpectrum :
      (fun i : Fin 4 => (if i = 0 then (-1 : Real) else 1) *
        (if i = 0 then (-1 : Real) else 1)) = fun _ => 1 := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [hSpectrum, Matrix.diagonal_one]

@[simp]
theorem mixedMetricDirection_zero_one : mixedMetricDirection 0 1 = -1 := by
  norm_num [mixedMetricDirection, Matrix.single]

@[simp]
theorem mixedMetricDirection_one_zero : mixedMetricDirection 1 0 = 1 := by
  norm_num [mixedMetricDirection, Matrix.single]

/-- The obstructed direction is a genuine symmetric metric variation after
lowering its first index by η. -/
theorem mixedMetricDirection_eta_symmetric :
    (mixedRoot * mixedMetricDirection).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [mixedRoot, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> norm_num [mixedMetricDirection, Matrix.single]

/-- Opposite root eigenvalues force this Sylvester entry to vanish. -/
theorem mixedRoot_sylvester_zero_one (variation : Matrix4) :
    sylvesterOperator mixedRoot variation 0 1 = 0 := by
  rw [mixedRoot, diagonal_sylvester_entry]
  norm_num

/-- No matrix solves the linearized square-root equation for this metric direction. -/
theorem mixedRoot_sylvester_ne_direction (variation : Matrix4) :
    sylvesterOperator mixedRoot variation ≠ mixedMetricDirection := by
  intro hEquation
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 1) hEquation
  rw [mixedRoot_sylvester_zero_one, mixedMetricDirection_zero_one] at hEntry
  norm_num at hEntry

theorem mixedRoot_no_sylvesterInverse :
    ¬ Nonempty (SylvesterInverseWitness mixedRoot) := by
  rintro ⟨inverse⟩
  exact mixedRoot_sylvester_ne_direction (inverse.inverse mixedMetricDirection)
    (inverse.rightInverse mixedMetricDirection)

/-- Even a local differentiable selector along I+tA cannot pass through B.
The square equation is required only near zero. -/
theorem mixedRoot_no_hasFDerivAt_selector
    (root : Real → Matrix4) (derivative : Real →L[Real] Matrix4)
    (hZero : root 0 = mixedRoot)
    (hSquare : (fun t => squareMap (root t)) =ᶠ[𝓝 (0 : Real)]
      (fun t => (1 : Matrix4) + t • mixedMetricDirection)) :
    ¬ HasFDerivAt root derivative 0 := by
  intro hRoot
  have hTarget : HasFDerivAt (fun t : Real => (1 : Matrix4) + t • mixedMetricDirection)
      ((ContinuousLinearMap.id Real Real).smulRight mixedMetricDirection) 0 :=
    ((hasFDerivAt_id (0 : Real)).smul_const mixedMetricDirection).const_add 1
  have hComposite := (squareMap_hasFDerivAt (root 0)).comp 0 hRoot
  have hEquation := (hComposite.congr_of_eventuallyEq hSquare.symm).unique hTarget
  have hDirection := congrArg (fun operator : Real →L[Real] Matrix4 => operator 1) hEquation
  change sylvesterOperator (root 0) (derivative 1) = (1 : Real) • mixedMetricDirection at hDirection
  have hImpossible : sylvesterOperator mixedRoot (derivative 1) = mixedMetricDirection := by
    simpa only [hZero, one_smul] using hDirection
  exact mixedRoot_sylvester_ne_direction (derivative 1) hImpossible

theorem mixedRoot_no_differentiableAt_selector
    (root : Real → Matrix4) (hZero : root 0 = mixedRoot)
    (hSquare : (fun t => squareMap (root t)) =ᶠ[𝓝 (0 : Real)]
      (fun t => (1 : Matrix4) + t • mixedMetricDirection)) :
    ¬ DifferentiableAt Real root 0 := by
  intro hRoot
  exact mixedRoot_no_hasFDerivAt_selector root _ hZero hSquare hRoot.hasFDerivAt

/-- The unrestricted square identity admits a root at which an allowed
metric direction has no differentiable local root lift. -/
theorem mixed_root_metric_chart_obstruction_gate :
    mixedRoot * mixedRoot = 1 ∧
      (mixedRoot * mixedMetricDirection).IsSymm ∧
      (∀ variation : Matrix4, sylvesterOperator mixedRoot variation ≠ mixedMetricDirection) ∧
      (∀ root : Real → Matrix4, root 0 = mixedRoot →
        (fun t => squareMap (root t)) =ᶠ[𝓝 (0 : Real)]
          (fun t => (1 : Matrix4) + t • mixedMetricDirection) →
        ¬ DifferentiableAt Real root 0) :=
  ⟨mixedRoot_square, mixedMetricDirection_eta_symmetric,
    mixedRoot_sylvester_ne_direction, mixedRoot_no_differentiableAt_selector⟩

end
end P0EFTJanusMixedRootMetricChartObstruction4D
end JanusFormal
