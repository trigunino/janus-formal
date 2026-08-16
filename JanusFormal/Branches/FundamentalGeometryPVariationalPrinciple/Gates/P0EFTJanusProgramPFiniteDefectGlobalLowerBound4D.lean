import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShift4D

/-!
# Global lower bound from coercivity off a finite defect

Let `H` be a bounded operator and `P` an idempotent finite-range defect with
`PH = HP = 0`.  If `H` is coercive on `ker P`, then no independent global
estimate for `H + P` is required.

Indeed, writing `x = (x - Px) + Px`, one has

* `P(x - Px) = 0`;
* `H(x - Px) = Hx`;
* `Px = P((H + P)x)`;
* `Hx = (H + P)x - Px`.

The operator norm of `P` and the off-defect coercivity therefore give the
explicit estimate

`‖x‖ ≤ (c⁻¹ (1 + ‖P‖) + ‖P‖) ‖(H + P)x‖`.

This is purely Banach-space algebra.  No orthogonality or spectral theorem is
used at this stage.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Explicit norm-control constant for the finite-defect shift. -/
def finiteDefectShiftControlConstant
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) : NNReal :=
  ⟨data.coercivityConstant⁻¹ * (1 + ‖data.projection‖) +
      ‖data.projection‖,
    add_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))
        (add_nonneg zero_le_one (norm_nonneg _)))
      (norm_nonneg _)⟩

/-- The projection of the shifted value is exactly the defect component. -/
theorem projection_finiteDefectShiftedOperator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    data.projection (finiteDefectShiftedOperator operator data vector) =
      data.projection vector := by
  change data.projection (operator vector + data.projection vector) =
    data.projection vector
  rw [map_add, data.projection_annihilates_operator,
    data.projection_idempotent, zero_add]

/-- The defect component is controlled by the shifted value. -/
theorem projection_norm_le_shifted
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    ‖data.projection vector‖ ≤
      ‖data.projection‖ *
        ‖finiteDefectShiftedOperator operator data vector‖ := by
  rw [← projection_finiteDefectShiftedOperator operator data vector]
  exact data.projection.le_opNorm
    (finiteDefectShiftedOperator operator data vector)

/-- The operator component is controlled by the shifted value and the norm of
`P`. -/
theorem operator_norm_le_shifted
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    ‖operator vector‖ ≤
      (1 + ‖data.projection‖) *
        ‖finiteDefectShiftedOperator operator data vector‖ := by
  have hOperator :
      operator vector =
        finiteDefectShiftedOperator operator data vector -
          data.projection vector := by
    change operator vector =
      operator vector + data.projection vector - data.projection vector
    abel
  calc
    ‖operator vector‖ =
        ‖finiteDefectShiftedOperator operator data vector -
          data.projection vector‖ := by rw [hOperator]
    _ ≤ ‖finiteDefectShiftedOperator operator data vector‖ +
        ‖data.projection vector‖ := norm_sub_le _ _
    _ ≤ ‖finiteDefectShiftedOperator operator data vector‖ +
        ‖data.projection‖ *
          ‖finiteDefectShiftedOperator operator data vector‖ :=
      add_le_add_left (projection_norm_le_shifted operator data vector) _
    _ = (1 + ‖data.projection‖) *
        ‖finiteDefectShiftedOperator operator data vector‖ := by ring

/-- Coercivity on `ker P` controls the complementary component of every
vector. -/
theorem complement_norm_le_operator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    ‖vector - data.projection vector‖ ≤
      data.coercivityConstant⁻¹ * ‖operator vector‖ := by
  have hProjection :
      data.projection (vector - data.projection vector) = 0 := by
    rw [map_sub, data.projection_idempotent]
    exact sub_self _
  have hOperator :
      operator (vector - data.projection vector) = operator vector := by
    rw [map_sub, data.operator_annihilates_projection, sub_zero]
  have hCoercive :=
    data.coercive_off_defect (vector - data.projection vector) hProjection
  rw [hOperator] at hCoercive
  have hNonzero : data.coercivityConstant ≠ 0 :=
    ne_of_gt data.coercivityConstant_pos
  calc
    ‖vector - data.projection vector‖ =
        data.coercivityConstant⁻¹ *
          (data.coercivityConstant *
            ‖vector - data.projection vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hNonzero, one_mul]
    _ ≤ data.coercivityConstant⁻¹ * ‖operator vector‖ :=
      mul_le_mul_of_nonneg_left hCoercive
        (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))

/-- Global lower bound for the shifted operator, derived from the original
off-defect coercivity packet. -/
theorem finiteDefectShiftedOperator_globalLowerBound
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    ‖vector‖ ≤
      (finiteDefectShiftControlConstant operator data : Real) *
        ‖finiteDefectShiftedOperator operator data vector‖ := by
  have hDecomposition :
      vector = (vector - data.projection vector) + data.projection vector := by
    abel
  calc
    ‖vector‖ =
        ‖(vector - data.projection vector) + data.projection vector‖ := by
      rw [hDecomposition]
    _ ≤ ‖vector - data.projection vector‖ +
        ‖data.projection vector‖ := norm_add_le _ _
    _ ≤ data.coercivityConstant⁻¹ * ‖operator vector‖ +
        ‖data.projection‖ *
          ‖finiteDefectShiftedOperator operator data vector‖ :=
      add_le_add
        (complement_norm_le_operator operator data vector)
        (projection_norm_le_shifted operator data vector)
    _ ≤ data.coercivityConstant⁻¹ *
          ((1 + ‖data.projection‖) *
            ‖finiteDefectShiftedOperator operator data vector‖) +
        ‖data.projection‖ *
          ‖finiteDefectShiftedOperator operator data vector‖ := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left
          (operator_norm_le_shifted operator data vector)
          (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))) _
    _ = (finiteDefectShiftControlConstant operator data : Real) *
        ‖finiteDefectShiftedOperator operator data vector‖ := by
      rfl

/-- Public checkpoint: the direct global estimate is a theorem, not an extra
field of the finite-defect coercivity data. -/
theorem finite_defect_global_lower_bound_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    ∀ vector,
      ‖vector‖ ≤
        (finiteDefectShiftControlConstant operator data : Real) *
          ‖finiteDefectShiftedOperator operator data vector‖ :=
  finiteDefectShiftedOperator_globalLowerBound operator data

end
end P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D
end JanusFormal
