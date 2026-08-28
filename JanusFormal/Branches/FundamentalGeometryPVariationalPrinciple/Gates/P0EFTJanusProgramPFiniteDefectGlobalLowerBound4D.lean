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

/-- The part of finite-defect shift data needed for norm control.  In
particular, no finite-dimensionality assumption on the projection range is
required. -/
structure FiniteDefectShiftControlData
    (operator : E →L[Real] E) where
  projection : E →L[Real] E
  projection_idempotent : ∀ vector,
    projection (projection vector) = projection vector
  projection_annihilates_operator : ∀ vector,
    projection (operator vector) = 0
  operator_annihilates_projection : ∀ vector,
    operator (projection vector) = 0
  coercivityConstant : Real
  coercivityConstant_pos : 0 < coercivityConstant
  coercive_off_defect : ∀ vector, projection vector = 0 →
    coercivityConstant * ‖vector‖ ≤ ‖operator vector‖

/-- Forget the finite-dimensionality witness from the historical coercive-shift
packet. -/
def FiniteDefectCoerciveShiftData.toShiftControlData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    FiniteDefectShiftControlData operator where
  projection := data.projection
  projection_idempotent := data.projection_idempotent
  projection_annihilates_operator := data.projection_annihilates_operator
  operator_annihilates_projection := data.operator_annihilates_projection
  coercivityConstant := data.coercivityConstant
  coercivityConstant_pos := data.coercivityConstant_pos
  coercive_off_defect := data.coercive_off_defect

/-- The shifted operator associated with lightweight norm-control data. -/
def finiteDefectShiftControlOperator
    (operator : E →L[Real] E)
    (data : FiniteDefectShiftControlData operator) : E →L[Real] E :=
  operator + data.projection

/-- Explicit global norm-control constant, requiring no finite-rank witness. -/
def finiteDefectShiftControlBound
    (operator : E →L[Real] E)
    (data : FiniteDefectShiftControlData operator) : NNReal :=
  ⟨data.coercivityConstant⁻¹ * (1 + ‖data.projection‖) +
      ‖data.projection‖,
    add_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))
        (add_nonneg zero_le_one (norm_nonneg _)))
      (norm_nonneg _)⟩

/-- Explicit control constant from only a projection and a positive coercivity
constant. -/
def finiteDefectShiftControlBoundRaw
    (projection : E →L[Real] E)
    (coercivityConstant : Real)
    (coercivityConstant_pos : 0 < coercivityConstant) : NNReal :=
  ⟨coercivityConstant⁻¹ * (1 + ‖projection‖) + ‖projection‖,
    add_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (le_of_lt coercivityConstant_pos))
        (add_nonneg zero_le_one (norm_nonneg _)))
      (norm_nonneg _)⟩

/-- Global lower bound from the lightweight finite-defect control packet. -/
theorem finiteDefectShiftControl_globalLowerBound
    (operator : E →L[Real] E)
    (data : FiniteDefectShiftControlData operator)
    (vector : E) :
    ‖vector‖ ≤
      (finiteDefectShiftControlBound operator data : Real) *
        ‖finiteDefectShiftControlOperator operator data vector‖ := by
  have hProjected :
      data.projection (finiteDefectShiftControlOperator operator data vector) =
        data.projection vector := by
    change data.projection (operator vector + data.projection vector) =
      data.projection vector
    rw [map_add, data.projection_annihilates_operator,
      data.projection_idempotent, zero_add]
  have hProjectionNorm :
      ‖data.projection vector‖ ≤
        ‖data.projection‖ *
          ‖finiteDefectShiftControlOperator operator data vector‖ := by
    rw [← hProjected]
    exact data.projection.le_opNorm
      (finiteDefectShiftControlOperator operator data vector)
  have hOperatorNorm :
      ‖operator vector‖ ≤
        (1 + ‖data.projection‖) *
          ‖finiteDefectShiftControlOperator operator data vector‖ := by
    have hOperator :
        operator vector =
          finiteDefectShiftControlOperator operator data vector -
            data.projection vector := by
      change operator vector =
        operator vector + data.projection vector - data.projection vector
      abel
    calc
      ‖operator vector‖ =
          ‖finiteDefectShiftControlOperator operator data vector -
            data.projection vector‖ := by rw [hOperator]
      _ ≤ ‖finiteDefectShiftControlOperator operator data vector‖ +
          ‖data.projection vector‖ := norm_sub_le _ _
      _ ≤ ‖finiteDefectShiftControlOperator operator data vector‖ +
          ‖data.projection‖ *
            ‖finiteDefectShiftControlOperator operator data vector‖ :=
        add_le_add_right hProjectionNorm _
      _ = (1 + ‖data.projection‖) *
          ‖finiteDefectShiftControlOperator operator data vector‖ := by ring
  have hComplementNorm :
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
  have hDecomposition :
      vector = (vector - data.projection vector) + data.projection vector := by
    abel
  calc
    ‖vector‖ =
        ‖(vector - data.projection vector) + data.projection vector‖ := by
      exact congrArg norm hDecomposition
    _ ≤ ‖vector - data.projection vector‖ +
        ‖data.projection vector‖ := norm_add_le _ _
    _ ≤ data.coercivityConstant⁻¹ * ‖operator vector‖ +
        ‖data.projection‖ *
          ‖finiteDefectShiftControlOperator operator data vector‖ :=
      add_le_add hComplementNorm hProjectionNorm
    _ ≤ data.coercivityConstant⁻¹ *
          ((1 + ‖data.projection‖) *
            ‖finiteDefectShiftControlOperator operator data vector‖) +
        ‖data.projection‖ *
          ‖finiteDefectShiftControlOperator operator data vector‖ := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hOperatorNorm
          (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))) _
    _ = (finiteDefectShiftControlBound operator data : Real) *
        ‖finiteDefectShiftControlOperator operator data vector‖ := by
      change
        data.coercivityConstant⁻¹ *
            ((1 + ‖data.projection‖) *
              ‖finiteDefectShiftControlOperator operator data vector‖) +
          ‖data.projection‖ *
              ‖finiteDefectShiftControlOperator operator data vector‖ =
          (data.coercivityConstant⁻¹ * (1 + ‖data.projection‖) +
              ‖data.projection‖) *
            ‖finiteDefectShiftControlOperator operator data vector‖
      ring

/-- Raw global lower bound without a finite-defect data packet or any
finite-dimensionality assumption. -/
theorem finiteDefectShiftControl_globalLowerBound_raw
    (operator projection : E →L[Real] E)
    (projection_idempotent : ∀ vector,
      projection (projection vector) = projection vector)
    (projection_annihilates_operator : ∀ vector,
      projection (operator vector) = 0)
    (operator_annihilates_projection : ∀ vector,
      operator (projection vector) = 0)
    (coercivityConstant : Real)
    (coercivityConstant_pos : 0 < coercivityConstant)
    (coercive_off_defect : ∀ vector, projection vector = 0 →
      coercivityConstant * ‖vector‖ ≤ ‖operator vector‖)
    (vector : E) :
    ‖vector‖ ≤
      (finiteDefectShiftControlBoundRaw projection coercivityConstant
        coercivityConstant_pos : Real) *
        ‖(operator + projection) vector‖ := by
  let data : FiniteDefectShiftControlData operator := {
    projection
    projection_idempotent
    projection_annihilates_operator
    operator_annihilates_projection
    coercivityConstant
    coercivityConstant_pos
    coercive_off_defect
  }
  simpa [data, finiteDefectShiftControlOperator,
    finiteDefectShiftControlBound, finiteDefectShiftControlBoundRaw] using
    finiteDefectShiftControl_globalLowerBound operator data vector

/-- Pointwise form of the raw shifted lower bound. -/
theorem finiteDefectShiftControl_globalLowerBound_raw_apply
    (operator projection : E →L[Real] E)
    (projection_idempotent : ∀ vector,
      projection (projection vector) = projection vector)
    (projection_annihilates_operator : ∀ vector,
      projection (operator vector) = 0)
    (operator_annihilates_projection : ∀ vector,
      operator (projection vector) = 0)
    (coercivityConstant : Real)
    (coercivityConstant_pos : 0 < coercivityConstant)
    (coercive_off_defect : ∀ vector, projection vector = 0 →
      coercivityConstant * ‖vector‖ ≤ ‖operator vector‖)
    (vector : E) :
    ‖vector‖ ≤
      (finiteDefectShiftControlBoundRaw projection coercivityConstant
        coercivityConstant_pos : Real) *
        ‖operator vector + projection vector‖ := by
  simpa only [add_apply] using
    finiteDefectShiftControl_globalLowerBound_raw operator projection
      projection_idempotent projection_annihilates_operator
      operator_annihilates_projection coercivityConstant
      coercivityConstant_pos coercive_off_defect vector

/-- Explicit norm-control constant for a purely pointwise finite-defect
shift. -/
def finiteDefectPointwiseShiftControlBound
    (coercivityConstant : Real)
    (coercivityConstant_pos : 0 < coercivityConstant)
    (projectionBound : NNReal) : NNReal :=
  ⟨coercivityConstant⁻¹ * (1 + (projectionBound : Real)) + projectionBound,
    by positivity⟩

/-- Purely pointwise global lower bound.  It only uses the additive identities
needed by the proof and a supplied norm bound for the projection. -/
theorem finiteDefectPointwiseShift_globalLowerBound
    {F : Type*} [NormedAddCommGroup F]
    (operator projection : F → F)
    (operator_map_sub : ∀ x y,
      operator (x - y) = operator x - operator y)
    (projection_map_add : ∀ x y,
      projection (x + y) = projection x + projection y)
    (projection_map_sub : ∀ x y,
      projection (x - y) = projection x - projection y)
    (projection_idempotent : ∀ x,
      projection (projection x) = projection x)
    (projection_annihilates_operator : ∀ x,
      projection (operator x) = 0)
    (operator_annihilates_projection : ∀ x,
      operator (projection x) = 0)
    (coercivityConstant : Real)
    (coercivityConstant_pos : 0 < coercivityConstant)
    (coercive_off_defect : ∀ x, projection x = 0 →
      coercivityConstant * ‖x‖ ≤ ‖operator x‖)
    (projectionBound : NNReal)
    (projection_norm_le : ∀ x,
      ‖projection x‖ ≤ (projectionBound : Real) * ‖x‖)
    (vector : F) :
    ‖vector‖ ≤
      (finiteDefectPointwiseShiftControlBound coercivityConstant
        coercivityConstant_pos projectionBound : Real) *
        ‖operator vector + projection vector‖ := by
  have hProjected :
      projection (operator vector + projection vector) = projection vector := by
    rw [projection_map_add, projection_annihilates_operator,
      projection_idempotent, zero_add]
  have hProjectionNorm :
      ‖projection vector‖ ≤
        (projectionBound : Real) *
          ‖operator vector + projection vector‖ := by
    calc
      ‖projection vector‖ =
          ‖projection (operator vector + projection vector)‖ :=
        congrArg norm hProjected.symm
      _ ≤ (projectionBound : Real) *
          ‖operator vector + projection vector‖ :=
        projection_norm_le (operator vector + projection vector)
  have hOperatorNorm :
      ‖operator vector‖ ≤
        (1 + (projectionBound : Real)) *
          ‖operator vector + projection vector‖ := by
    have hOperator :
        operator vector =
          (operator vector + projection vector) - projection vector := by
      abel
    calc
      ‖operator vector‖ =
          ‖(operator vector + projection vector) - projection vector‖ := by
        exact congrArg norm hOperator
      _ ≤ ‖operator vector + projection vector‖ + ‖projection vector‖ :=
        norm_sub_le _ _
      _ ≤ ‖operator vector + projection vector‖ +
          (projectionBound : Real) *
            ‖operator vector + projection vector‖ :=
        add_le_add_right hProjectionNorm _
      _ = (1 + (projectionBound : Real)) *
          ‖operator vector + projection vector‖ := by ring
  have hComplementNorm :
      ‖vector - projection vector‖ ≤
        coercivityConstant⁻¹ * ‖operator vector‖ := by
    have hProjection : projection (vector - projection vector) = 0 := by
      rw [projection_map_sub, projection_idempotent]
      exact sub_self _
    have hOperator :
        operator (vector - projection vector) = operator vector := by
      rw [operator_map_sub, operator_annihilates_projection, sub_zero]
    have hCoercive :=
      coercive_off_defect (vector - projection vector) hProjection
    rw [hOperator] at hCoercive
    have hNonzero : coercivityConstant ≠ 0 :=
      ne_of_gt coercivityConstant_pos
    calc
      ‖vector - projection vector‖ =
          coercivityConstant⁻¹ *
            (coercivityConstant * ‖vector - projection vector‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hNonzero, one_mul]
      _ ≤ coercivityConstant⁻¹ * ‖operator vector‖ :=
        mul_le_mul_of_nonneg_left hCoercive
          (inv_nonneg.mpr (le_of_lt coercivityConstant_pos))
  have hDecomposition :
      vector = (vector - projection vector) + projection vector := by
    abel
  calc
    ‖vector‖ = ‖(vector - projection vector) + projection vector‖ := by
      exact congrArg norm hDecomposition
    _ ≤ ‖vector - projection vector‖ + ‖projection vector‖ := norm_add_le _ _
    _ ≤ coercivityConstant⁻¹ * ‖operator vector‖ +
        (projectionBound : Real) * ‖operator vector + projection vector‖ :=
      add_le_add hComplementNorm hProjectionNorm
    _ ≤ coercivityConstant⁻¹ *
          ((1 + (projectionBound : Real)) *
            ‖operator vector + projection vector‖) +
        (projectionBound : Real) *
          ‖operator vector + projection vector‖ := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hOperatorNorm
          (inv_nonneg.mpr (le_of_lt coercivityConstant_pos))) _
    _ = (finiteDefectPointwiseShiftControlBound coercivityConstant
          coercivityConstant_pos projectionBound : Real) *
        ‖operator vector + projection vector‖ := by
      change
        coercivityConstant⁻¹ *
            ((1 + (projectionBound : Real)) *
              ‖operator vector + projection vector‖) +
          (projectionBound : Real) * ‖operator vector + projection vector‖ =
          (coercivityConstant⁻¹ * (1 + (projectionBound : Real)) +
              projectionBound) * ‖operator vector + projection vector‖
      ring

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
      add_le_add_right (projection_norm_le_shifted operator data vector) _
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
      exact congrArg norm hDecomposition
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
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left
          (operator_norm_le_shifted operator data vector)
          (inv_nonneg.mpr (le_of_lt data.coercivityConstant_pos))) _
    _ = (finiteDefectShiftControlConstant operator data : Real) *
        ‖finiteDefectShiftedOperator operator data vector‖ := by
      change
        data.coercivityConstant⁻¹ *
            ((1 + ‖data.projection‖) *
              ‖finiteDefectShiftedOperator operator data vector‖) +
          ‖data.projection‖ *
              ‖finiteDefectShiftedOperator operator data vector‖ =
          (data.coercivityConstant⁻¹ * (1 + ‖data.projection‖) +
              ‖data.projection‖) *
            ‖finiteDefectShiftedOperator operator data vector‖
      ring

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
