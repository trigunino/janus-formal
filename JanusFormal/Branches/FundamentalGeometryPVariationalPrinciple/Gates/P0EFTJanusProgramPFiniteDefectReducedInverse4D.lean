import Mathlib.Analysis.Normed.Operator.Banach
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedOperator4D

/-!
# Continuous inverse of the reduced finite-defect operator

The reduced operator on `ker P` is a bounded bijection between Banach spaces.
The bounded inverse theorem therefore upgrades it to a continuous linear
equivalence.  Its inverse is the canonical reduced Green operator, with norm
controlled by the reciprocal coercivity constant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedInverse4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedOperator4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

local instance finiteDefectKerCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Continuous linear equivalence induced by the reduced Hessian. -/
noncomputable def finiteDefectReducedEquiv
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    data.projection.ker ≃L[Real] data.projection.ker :=
  ContinuousLinearEquiv.ofBijective
    (finiteDefectReducedOperator operator data)
    (LinearMap.ker_eq_bot.mpr
      (finiteDefectReducedOperator_injective operator data))
    (LinearMap.range_eq_top.mpr
      (finiteDefectReducedOperator_surjective operator data hShiftSurjective))

/-- Canonical reduced Green operator. -/
noncomputable def finiteDefectReducedInverse
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    data.projection.ker →L[Real] data.projection.ker :=
  (finiteDefectReducedEquiv operator data hShiftSurjective).symm

@[simp]
theorem finiteDefectReducedOperator_inverse
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (vector : data.projection.ker) :
    finiteDefectReducedOperator operator data
        (finiteDefectReducedInverse operator data hShiftSurjective vector) =
      vector :=
  by
    simpa [finiteDefectReducedInverse, finiteDefectReducedEquiv] using
      (finiteDefectReducedEquiv operator data hShiftSurjective).apply_symm_apply
        vector

@[simp]
theorem finiteDefectReducedInverse_operator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (vector : data.projection.ker) :
    finiteDefectReducedInverse operator data hShiftSurjective
        (finiteDefectReducedOperator operator data vector) =
      vector :=
  by
    simpa [finiteDefectReducedInverse, finiteDefectReducedEquiv] using
      (finiteDefectReducedEquiv operator data hShiftSurjective).symm_apply_apply
        vector

/-- Pointwise norm control of the reduced inverse. -/
theorem finiteDefectReducedInverse_norm_le
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (vector : data.projection.ker) :
    ‖finiteDefectReducedInverse operator data hShiftSurjective vector‖ ≤
      data.coercivityConstant⁻¹ * ‖vector‖ := by
  let preimage := finiteDefectReducedInverse operator data hShiftSurjective
    vector
  have hLower := finiteDefectReducedOperator_lowerBound operator data preimage
  rw [finiteDefectReducedOperator_inverse operator data hShiftSurjective vector]
    at hLower
  have hNonzero : data.coercivityConstant ≠ 0 :=
    ne_of_gt data.coercivityConstant_pos
  calc
    ‖preimage‖ = data.coercivityConstant⁻¹ *
        (data.coercivityConstant * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hNonzero, one_mul]
    _ ≤ data.coercivityConstant⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))

/-- Operator-norm bound for the reduced Green operator. -/
theorem finiteDefectReducedInverse_opNorm_le
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    ‖finiteDefectReducedInverse operator data hShiftSurjective‖ ≤
      data.coercivityConstant⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (finiteDefectReducedInverse operator data hShiftSurjective)
    (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))
  intro vector
  simpa using finiteDefectReducedInverse_norm_le operator data
    hShiftSurjective vector

/-- Public reduced inverse checkpoint. -/
theorem finite_defect_reduced_inverse_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    Function.LeftInverse
        (finiteDefectReducedInverse operator data hShiftSurjective)
        (finiteDefectReducedOperator operator data) ∧
      Function.RightInverse
        (finiteDefectReducedInverse operator data hShiftSurjective)
        (finiteDefectReducedOperator operator data) ∧
      ‖finiteDefectReducedInverse operator data hShiftSurjective‖ ≤
        data.coercivityConstant⁻¹ := by
  exact
    ⟨finiteDefectReducedInverse_operator operator data hShiftSurjective,
      finiteDefectReducedOperator_inverse operator data hShiftSurjective,
      finiteDefectReducedInverse_opNorm_le operator data hShiftSurjective⟩

end
end P0EFTJanusProgramPFiniteDefectReducedInverse4D
end JanusFormal
