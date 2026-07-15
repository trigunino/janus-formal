import Mathlib

namespace JanusFormal
namespace P0EFTJanusScalarConstraintSchurGate

set_option autoImplicit false

/-- Generic two-scalar kinetic quadratic form. -/
def scalarKinetic
    (plusCoefficient mixing auxiliaryCoefficient plusMode auxiliaryMode : ℝ) : ℝ :=
  plusCoefficient * plusMode ^ 2 +
    2 * mixing * plusMode * auxiliaryMode +
    auxiliaryCoefficient * auxiliaryMode ^ 2

/-- Algebraic auxiliary-field solution from `b x + c y = 0`. -/
noncomputable def auxiliaryConstraintSolution
    (mixing auxiliaryCoefficient plusMode : ℝ) : ℝ :=
  -(mixing / auxiliaryCoefficient) * plusMode

/-- Exact Schur-complement reduction after imposing the auxiliary constraint. -/
theorem scalar_kinetic_schur_reduction
    (plusCoefficient mixing auxiliaryCoefficient plusMode : ℝ)
    (hAuxiliary : auxiliaryCoefficient ≠ 0) :
    scalarKinetic plusCoefficient mixing auxiliaryCoefficient plusMode
        (auxiliaryConstraintSolution mixing auxiliaryCoefficient plusMode) =
      (plusCoefficient - mixing ^ 2 / auxiliaryCoefficient) * plusMode ^ 2 := by
  unfold scalarKinetic auxiliaryConstraintSolution
  field_simp [hAuxiliary]
  ring

/-- Positive determinant and positive auxiliary coefficient give a safe mode. -/
theorem schur_reduced_scalar_kinetic_positive
    (plusCoefficient mixing auxiliaryCoefficient plusMode : ℝ)
    (hAuxiliary : 0 < auxiliaryCoefficient)
    (hDeterminant : 0 < plusCoefficient * auxiliaryCoefficient - mixing ^ 2)
    (hMode : plusMode ≠ 0) :
    0 < scalarKinetic plusCoefficient mixing auxiliaryCoefficient plusMode
        (auxiliaryConstraintSolution mixing auxiliaryCoefficient plusMode) := by
  rw [scalar_kinetic_schur_reduction _ _ _ _ (ne_of_gt hAuxiliary)]
  have hReduced :
      0 < plusCoefficient - mixing ^ 2 / auxiliaryCoefficient := by
    have hRewrite :
        plusCoefficient - mixing ^ 2 / auxiliaryCoefficient =
          (plusCoefficient * auxiliaryCoefficient - mixing ^ 2) /
            auxiliaryCoefficient := by
      field_simp
    rw [hRewrite]
    exact div_pos hDeterminant hAuxiliary
  exact mul_pos hReduced (sq_pos_of_ne_zero hMode)

/--
Closure status: the algebraic gate is exact, but Janus must derive the lapse or
boundary equation that makes the second scalar genuinely auxiliary.
-/
structure ScalarConstraintClosureStatus where
  fullScalarQuadraticActionDerived : Prop
  lapseOrBoundaryConstraintDerived : Prop
  auxiliaryCoefficientPositive : Prop
  schurDeterminantPositive : Prop
  reducedScalarNoGhost : Prop
  gradientStabilityProved : Prop

def scalarConstraintClosed (s : ScalarConstraintClosureStatus) : Prop :=
  s.fullScalarQuadraticActionDerived ∧
  s.lapseOrBoundaryConstraintDerived ∧
  s.auxiliaryCoefficientPositive ∧
  s.schurDeterminantPositive ∧
  s.reducedScalarNoGhost ∧
  s.gradientStabilityProved

end P0EFTJanusScalarConstraintSchurGate
end JanusFormal
