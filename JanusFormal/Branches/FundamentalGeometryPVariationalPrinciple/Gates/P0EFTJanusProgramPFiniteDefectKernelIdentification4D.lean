import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShift4D

/-!
# Exact kernel identification for a finite-defect coercive operator

For the finite-defect coercivity packet, the range of the defect projector is
not merely a finite-dimensional space containing some zero modes.  It is
exactly the kernel of the operator.

The inclusion `range P ⊆ ker H` is the stored relation `HP = 0`.  Conversely,
if `Hx = 0`, then `x - Px` lies in `ker P`, is also annihilated by `H`, and the
strict coercivity on `ker P` forces `x - Px = 0`.  Hence `x = Px`.

This module exposes the canonical zero-mode identification needed by the
Fredholm determinant and stability layers.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectKernelIdentification4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

private theorem operator_projection_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    operator (data.projection vector) = 0 := by
  exact data.operator_annihilates_projection vector

private theorem projection_operator_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    data.projection (operator vector) = 0 := by
  exact data.projection_annihilates_operator vector

private theorem projection_projection_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    data.projection (data.projection vector) = data.projection vector := by
  exact data.projection_idempotent vector

/-- The complement `x - Px` lies in the kernel of the projection. -/
theorem finiteDefect_complement_mem_projection_ker
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    vector - data.projection vector ∈ data.projection.ker := by
  apply LinearMap.mem_ker.mpr
  rw [map_sub]
  exact sub_eq_zero.mpr (data.projection_idempotent vector).symm

/-- The operator ignores the projected zero-mode component. -/
theorem finiteDefect_operator_complement
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    operator (vector - data.projection vector) = operator vector := by
  rw [map_sub, operator_projection_apply operator data, sub_zero]

/-- Every kernel vector is fixed by the defect projection. -/
theorem finiteDefect_projection_eq_self_of_mem_kernel
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E)
    (hKernel : vector ∈ operator.ker) :
    data.projection vector = vector := by
  have hOperator : operator vector = 0 := LinearMap.mem_ker.mp hKernel
  let complement := vector - data.projection vector
  have hProjection : complement ∈ data.projection.ker :=
    finiteDefect_complement_mem_projection_ker operator data vector
  have hComplementOperator : operator complement = 0 := by
    rw [finiteDefect_operator_complement operator data vector, hOperator]
  have hCoercive := data.coercive_off_defect complement hProjection
  rw [hComplementOperator, norm_zero] at hCoercive
  have hNorm : ‖complement‖ = 0 := by
    by_contra hNonzero
    have hNormPos : 0 < ‖complement‖ :=
      lt_of_le_of_ne (norm_nonneg complement) (Ne.symm hNonzero)
    have hProductPos :
        0 < data.coercivityConstant * ‖complement‖ :=
      mul_pos data.coercivityConstant_pos hNormPos
    linarith
  have hComplement : complement = 0 := norm_eq_zero.mp hNorm
  unfold complement at hComplement
  exact (sub_eq_zero.mp hComplement).symm

/-- Exact identification of the zero-mode space. -/
theorem finiteDefect_operator_ker_eq_projection_range
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    operator.ker = data.projection.range := by
  ext vector
  constructor
  · intro hKernel
    refine ⟨vector, ?_⟩
    exact finiteDefect_projection_eq_self_of_mem_kernel operator data vector
      hKernel
  · rintro ⟨source, rfl⟩
    exact LinearMap.mem_ker.mpr
      (operator_projection_apply operator data source)

/-- The finite defect is therefore the full kernel, not just an upper bound. -/
theorem finiteDefect_operator_kernel_finite
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    FiniteDimensional Real operator.ker := by
  rw [finiteDefect_operator_ker_eq_projection_range operator data]
  exact data.projection_range_finite

/-- Public decomposition checkpoint. -/
theorem finite_defect_kernel_identification_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    operator.ker = data.projection.range ∧
      FiniteDimensional Real operator.ker :=
  ⟨finiteDefect_operator_ker_eq_projection_range operator data,
    finiteDefect_operator_kernel_finite operator data⟩

end
end P0EFTJanusProgramPFiniteDefectKernelIdentification4D
end JanusFormal
