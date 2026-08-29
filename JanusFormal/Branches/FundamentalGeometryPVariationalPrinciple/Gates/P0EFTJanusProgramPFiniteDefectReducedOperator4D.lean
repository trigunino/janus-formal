import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectKernelIdentification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectRangeIdentification4D

/-!
# The reduced operator on the finite-defect complement

For a finite-defect coercive operator `H` with defect projection `P`, the
relation `PH = 0` makes `H` preserve `ker P`.  If `H + P` is surjective, the
restricted operator

`H_red : ker P → ker P`

is bijective.  Its injectivity and quantitative lower bound come directly from
the coercivity stored on `ker P`; its surjectivity is the exact range identity
`range H = ker P`.

This is the operator needed after removing zero modes.  No quotient choice or
new completion is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedOperator4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectKernelIdentification4D
open P0EFTJanusProgramPFiniteDefectRangeIdentification4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

private theorem projection_operator_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    data.projection (operator vector) = 0 := by
  exact data.projection_annihilates_operator vector

/-- Restriction of `H` to the complement of the finite defect. -/
def finiteDefectReducedOperator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    data.projection.ker →L[Real] data.projection.ker := by
  let linear : data.projection.ker →ₗ[Real] data.projection.ker :=
    { toFun := fun vector =>
        ⟨operator vector.1,
          LinearMap.mem_ker.mpr
            (projection_operator_apply operator data vector.1)⟩
      map_add' := by
        intro first second
        apply Subtype.ext
        exact map_add operator first.1 second.1
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        exact map_smul operator scalar vector.1 }
  exact linear.mkContinuous ‖operator‖ (by
    intro vector
    change ‖operator vector.1‖ ≤ ‖operator‖ * ‖vector.1‖
    exact operator.le_opNorm vector.1)

@[simp]
theorem finiteDefectReducedOperator_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : data.projection.ker) :
    (finiteDefectReducedOperator operator data vector).1 = operator vector.1 :=
  rfl

/-- The original coercivity is exactly the reduced lower bound. -/
theorem finiteDefectReducedOperator_lowerBound
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : data.projection.ker) :
    data.coercivityConstant * ‖vector‖ ≤
      ‖finiteDefectReducedOperator operator data vector‖ := by
  change data.coercivityConstant * ‖vector.1‖ ≤ ‖operator vector.1‖
  exact data.coercive_off_defect vector.1 vector.2

/-- Strict coercivity makes the reduced operator injective. -/
theorem finiteDefectReducedOperator_injective
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    Function.Injective (finiteDefectReducedOperator operator data) := by
  intro first second hEqual
  have hOperator : operator (first.1 - second.1) = 0 := by
    rw [map_sub]
    exact congrArg Subtype.val hEqual |> sub_eq_zero.mpr
  have hProjection : first.1 - second.1 ∈ data.projection.ker := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub, LinearMap.mem_ker.mp first.2, LinearMap.mem_ker.mp second.2,
      sub_zero]
  have hCoercive := data.coercive_off_defect
    (first.1 - second.1) hProjection
  rw [hOperator, norm_zero] at hCoercive
  have hNorm : ‖first.1 - second.1‖ = 0 := by
    by_contra hNonzero
    have hNormPos : 0 < ‖first.1 - second.1‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNonzero)
    have hProductPos :
        0 < data.coercivityConstant * ‖first.1 - second.1‖ :=
      mul_pos data.coercivityConstant_pos hNormPos
    linarith
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Surjectivity of the full shift makes the reduced operator surjective. -/
theorem finiteDefectReducedOperator_surjective
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    Function.Surjective (finiteDefectReducedOperator operator data) := by
  intro target
  have hTargetRange : target.1 ∈ operator.range :=
    finiteDefect_projection_ker_le_operator_range operator data
      hShiftSurjective target.2
  obtain ⟨source, hSource⟩ := hTargetRange
  let reducedSource : data.projection.ker :=
    ⟨source - data.projection source,
      finiteDefect_complement_mem_projection_ker operator data source⟩
  refine ⟨reducedSource, ?_⟩
  apply Subtype.ext
  change operator (source - data.projection source) = target.1
  rw [finiteDefect_operator_complement operator data source]
  exact hSource

/-- Quantitative reduced invertibility certificate. -/
structure FiniteDefectReducedOperatorCertificate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) : Prop where
  injective : Function.Injective (finiteDefectReducedOperator operator data)
  surjective : Function.Surjective (finiteDefectReducedOperator operator data)
  lowerBound : ∀ vector,
    data.coercivityConstant * ‖vector‖ ≤
      ‖finiteDefectReducedOperator operator data vector‖

/-- Construction of the reduced certificate. -/
def finiteDefectReducedOperatorCertificate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    FiniteDefectReducedOperatorCertificate operator data hShiftSurjective where
  injective := finiteDefectReducedOperator_injective operator data
  surjective := finiteDefectReducedOperator_surjective operator data
    hShiftSurjective
  lowerBound := finiteDefectReducedOperator_lowerBound operator data

/-- Public reduced-operator gate. -/
theorem finite_defect_reduced_operator_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    FiniteDefectReducedOperatorCertificate operator data hShiftSurjective :=
  finiteDefectReducedOperatorCertificate operator data hShiftSurjective

end
end P0EFTJanusProgramPFiniteDefectReducedOperator4D
end JanusFormal
