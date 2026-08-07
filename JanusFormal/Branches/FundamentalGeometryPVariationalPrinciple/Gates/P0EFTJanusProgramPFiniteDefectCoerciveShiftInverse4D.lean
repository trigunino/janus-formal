import Mathlib.Analysis.Normed.Module.OpenMapping
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShift4D

/-!
# Canonical inverse and parametrix of a coercive finite-defect shift

For a Banach space, coercivity off the finite defect makes `H + P` injective.
If the shifted operator is surjective, the open mapping theorem gives a bounded
inverse.  That inverse is automatically a generalized inverse for `H` and both
canonical defects are exactly `P`:

`QH = I - P`, `HQ = I - P`, `HQH = H`.

Thus H12 needs neither a supplied inverse nor separately supplied left/right
defects.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectCoerciveShiftInverse4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- The bounded equivalence furnished by bijectivity of the coercive shift. -/
noncomputable def finiteDefectShiftedEquiv_of_surjective
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    E ≃L[Real] E :=
  ContinuousLinearMap.continuousLinearEquivOfBijective
    (finiteDefectShiftedOperator operator data)
    (finiteDefectShiftedOperator_bijective_of_surjective operator data
      hSurjective)

/-- Canonical bounded parametrix: the inverse of `H + P`. -/
noncomputable def finiteDefectCanonicalParametrix
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    E →L[Real] E :=
  (finiteDefectShiftedEquiv_of_surjective operator data hSurjective).symm

private theorem shifted_apply_sub_projection
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    finiteDefectShiftedOperator operator data
        (vector - data.projection vector) =
      operator vector := by
  change
    operator (vector - data.projection vector) +
      data.projection (vector - data.projection vector) = operator vector
  rw [map_sub, map_sub, data.operator_annihilates_projection,
    data.projection_idempotent]
  simp

/-- The canonical parametrix composed after `H` is `I-P`. -/
theorem finiteDefectCanonicalParametrix_operator_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (vector : E) :
    finiteDefectCanonicalParametrix operator data hSurjective
        (operator vector) =
      vector - data.projection vector := by
  apply finiteDefectShiftedOperator_injective operator data
  rw [shifted_apply_sub_projection operator data vector]
  exact
    (finiteDefectShiftedEquiv_of_surjective operator data hSurjective).
      apply_symm_apply (operator vector)

/-- Applying the projection to the inverse of the shifted operator recovers the
projection of the original vector. -/
theorem projection_finiteDefectCanonicalParametrix_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (vector : E) :
    data.projection
        (finiteDefectCanonicalParametrix operator data hSurjective vector) =
      data.projection vector := by
  have hInverse :=
    (finiteDefectShiftedEquiv_of_surjective operator data hSurjective).
      apply_symm_apply vector
  have hApplied := congrArg data.projection hInverse
  change
    data.projection
        (operator
            (finiteDefectCanonicalParametrix operator data hSurjective vector) +
          data.projection
            (finiteDefectCanonicalParametrix operator data hSurjective vector)) =
      data.projection vector at hApplied
  rw [map_add, data.projection_annihilates_operator,
    data.projection_idempotent, zero_add] at hApplied
  exact hApplied

/-- `H` composed after the canonical parametrix is also `I-P`. -/
theorem operator_finiteDefectCanonicalParametrix_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (vector : E) :
    operator (finiteDefectCanonicalParametrix operator data hSurjective vector) =
      vector - data.projection vector := by
  have hInverse :=
    (finiteDefectShiftedEquiv_of_surjective operator data hSurjective).
      apply_symm_apply vector
  change
    operator (finiteDefectCanonicalParametrix operator data hSurjective vector) +
      data.projection
        (finiteDefectCanonicalParametrix operator data hSurjective vector) =
      vector at hInverse
  rw [projection_finiteDefectCanonicalParametrix_apply operator data hSurjective
    vector] at hInverse
  exact eq_sub_of_add_eq hInverse

/-- Continuous-linear-map form of `QH = I-P`. -/
theorem finiteDefectCanonicalParametrix_comp_operator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    (finiteDefectCanonicalParametrix operator data hSurjective).comp operator =
      ContinuousLinearMap.id Real E - data.projection := by
  ext vector
  exact finiteDefectCanonicalParametrix_operator_apply operator data
    hSurjective vector

/-- Continuous-linear-map form of `HQ = I-P`. -/
theorem operator_comp_finiteDefectCanonicalParametrix
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    operator.comp (finiteDefectCanonicalParametrix operator data hSurjective) =
      ContinuousLinearMap.id Real E - data.projection := by
  ext vector
  exact operator_finiteDefectCanonicalParametrix_apply operator data hSurjective
    vector

/-- The inverse of the shifted operator is a generalized inverse of `H`. -/
theorem operator_parametrix_operator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    (operator.comp
      (finiteDefectCanonicalParametrix operator data hSurjective)).comp
        operator = operator := by
  rw [operator_comp_finiteDefectCanonicalParametrix operator data hSurjective]
  ext vector
  simp [data.projection_annihilates_operator]

/-- Complete canonical-parametrix checkpoint. -/
theorem finite_defect_coercive_shift_inverse_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    ((finiteDefectCanonicalParametrix operator data hSurjective).comp operator =
      ContinuousLinearMap.id Real E - data.projection) ∧
    (operator.comp
      (finiteDefectCanonicalParametrix operator data hSurjective) =
        ContinuousLinearMap.id Real E - data.projection) ∧
    ((operator.comp
      (finiteDefectCanonicalParametrix operator data hSurjective)).comp
        operator = operator) :=
  ⟨finiteDefectCanonicalParametrix_comp_operator operator data hSurjective,
    operator_comp_finiteDefectCanonicalParametrix operator data hSurjective,
    operator_parametrix_operator operator data hSurjective⟩

end
end P0EFTJanusProgramPFiniteDefectCoerciveShiftInverse4D
end JanusFormal
