import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coercive finite-defect shifts

This file isolates the elementary functional-analysis step used by the H12
shifted-inverse route.  Let `H` be a bounded operator and let `P` be a
finite-range idempotent which is killed by `H` and kills the range of `H`.
If `H` is bounded below on `ker P`, then:

* `ker H` is contained in `range P`;
* `H + P` is injective;
* consequently, a separate surjectivity proof for `H + P` gives bijectivity.

Thus the shifted route does not need injectivity as an independent analytic
hypothesis.  No spectral theorem and no extra completion are used here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectCoerciveShift4D

set_option autoImplicit false
noncomputable section

open Set

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A finite-dimensional defect projector and a coercive estimate for the
operator on its complement. -/
structure FiniteDefectCoerciveShiftData
    (operator : E →L[Real] E) : Prop where
  projection : E →L[Real] E
  projection_idempotent : ∀ vector,
    projection (projection vector) = projection vector
  projection_annihilates_operator : ∀ vector,
    projection (operator vector) = 0
  operator_annihilates_projection : ∀ vector,
    operator (projection vector) = 0
  projection_range_finite : FiniteDimensional Real projection.range
  coercivityConstant : Real
  coercivityConstant_pos : 0 < coercivityConstant
  coercive_off_defect : ∀ vector, projection vector = 0 →
    coercivityConstant * ‖vector‖ ≤ ‖operator vector‖

/-- The bounded shifted operator used in the finite-defect construction. -/
def finiteDefectShiftedOperator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) : E →L[Real] E :=
  operator + data.projection

/-- The coercive estimate forces every zero mode of `operator` into the finite
range of the defect projector. -/
theorem operator_ker_le_projection_range
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    operator.ker ≤ data.projection.range := by
  intro vector hKernel
  have hComplementProjection :
      data.projection (vector - data.projection vector) = 0 := by
    rw [map_sub, data.projection_idempotent]
    exact sub_self _
  have hComplementOperator :
      operator (vector - data.projection vector) = 0 := by
    rw [map_sub, hKernel, data.operator_annihilates_projection]
    exact sub_self _
  have hBound := data.coercive_off_defect
    (vector - data.projection vector) hComplementProjection
  rw [hComplementOperator, norm_zero] at hBound
  have hNorm : ‖vector - data.projection vector‖ = 0 := by
    by_contra hNonzero
    have hNormPos : 0 < ‖vector - data.projection vector‖ :=
      norm_pos_iff.mpr hNonzero
    have hProductPos :
        0 < data.coercivityConstant *
          ‖vector - data.projection vector‖ :=
      mul_pos data.coercivityConstant_pos hNormPos
    exact (not_lt_of_ge hBound) hProductPos
  have hFixed : data.projection vector = vector := by
    have := norm_eq_zero.mp hNorm
    exact eq_of_sub_eq_zero this |>.symm
  exact ⟨vector, hFixed⟩

/-- The finite-defect shift is injective; no additional injectivity witness is
required by the H12 construction. -/
theorem finiteDefectShiftedOperator_injective
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    Function.Injective (finiteDefectShiftedOperator operator data) := by
  intro first second hEqual
  let difference := first - second
  have hShiftDifference :
      finiteDefectShiftedOperator operator data difference = 0 := by
    change
      finiteDefectShiftedOperator operator data first -
        finiteDefectShiftedOperator operator data second = 0
    rw [hEqual]
    exact sub_self _
  have hProjected : data.projection difference = 0 := by
    have hProjectedShift := congrArg data.projection hShiftDifference
    simp only [map_zero] at hProjectedShift
    change
      data.projection (operator difference + data.projection difference) = 0
        at hProjectedShift
    rw [map_add, data.projection_annihilates_operator,
      data.projection_idempotent, zero_add] at hProjectedShift
    exact hProjectedShift
  have hOperator : operator difference = 0 := by
    change operator difference + data.projection difference = 0 at hShiftDifference
    rw [hProjected, add_zero] at hShiftDifference
    exact hShiftDifference
  have hBound := data.coercive_off_defect difference hProjected
  rw [hOperator, norm_zero] at hBound
  have hDifferenceNorm : ‖difference‖ = 0 := by
    by_contra hNonzero
    have hNormPos : 0 < ‖difference‖ := norm_pos_iff.mpr hNonzero
    have hProductPos : 0 < data.coercivityConstant * ‖difference‖ :=
      mul_pos data.coercivityConstant_pos hNormPos
    exact (not_lt_of_ge hBound) hProductPos
  have hDifference : difference = 0 := norm_eq_zero.mp hDifferenceNorm
  exact sub_eq_zero.mp hDifference

/-- Therefore surjectivity is the only remaining range statement needed to
obtain a bijective shifted operator. -/
theorem finiteDefectShiftedOperator_bijective_of_surjective
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    Function.Bijective (finiteDefectShiftedOperator operator data) :=
  ⟨finiteDefectShiftedOperator_injective operator data, hSurjective⟩

/-- Public algebraic checkpoint for the finite-defect coercive shift. -/
theorem finite_defect_coercive_shift_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    operator.ker ≤ data.projection.range ∧
      Function.Injective (finiteDefectShiftedOperator operator data) :=
  ⟨operator_ker_le_projection_range operator data,
    finiteDefectShiftedOperator_injective operator data⟩

end
end P0EFTJanusProgramPFiniteDefectCoerciveShift4D
end JanusFormal
