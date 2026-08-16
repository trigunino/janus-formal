import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedSelfAdjointFredholmReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

/-!
# Canonical reduction on the orthogonal complement of the actual kernel

A finite-rank projection is useful for parametrix constructions, but it is not
part of the physical Hessian.  For a bounded self-adjoint operator `H`, the
canonical zero-mode-free space is simply

`(ker H)ᗮ`.

This file works directly on that subspace.  It proves that self-adjointness
makes the subspace invariant, restricts `H` to it, and shows that one positive
lower bound on the restriction gives a bounded bijection and a continuous
Green operator.  If the actual kernel is finite-dimensional, the same input
also gives closed range, Fredholmness and index zero.

No auxiliary projection, quotient, completion or replacement operator is
chosen.  The zero modes are definitionally the genuine kernel of `H`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusBoundedSelfAdjointFredholmReduction4D
open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- The canonical zero-mode-free Hilbert space of `operator`. -/
abbrev SelfAdjointKernelComplement (operator : E →L[Real] E) :=
  operator.kerᗮ

local instance selfAdjointKernelComplementCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- A self-adjoint operator maps the orthogonal complement of its kernel to
itself. -/
theorem selfAdjoint_operator_mem_kernelComplement
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (vector : SelfAdjointKernelComplement operator) :
    operator vector.1 ∈ operator.kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro zeroMode hZeroMode
  have hKernel : operator zeroMode = 0 :=
    LinearMap.mem_ker.mp hZeroMode
  calc
    inner Real (operator vector.1) zeroMode =
        inner Real vector.1 (operator zeroMode) :=
      hSelfAdjoint.isSymmetric vector.1 zeroMode
    _ = 0 := by rw [hKernel, inner_zero_right]

/-- Restriction of the same operator to the actual kernel complement. -/
def selfAdjointKernelComplementOperator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator := by
  let linear : SelfAdjointKernelComplement operator →ₗ[Real]
      SelfAdjointKernelComplement operator :=
    { toFun := fun vector =>
        ⟨operator vector.1,
          selfAdjoint_operator_mem_kernelComplement operator hSelfAdjoint
            vector⟩
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
theorem selfAdjointKernelComplementOperator_apply
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (vector : SelfAdjointKernelComplement operator) :
    (selfAdjointKernelComplementOperator operator hSelfAdjoint vector).1 =
      operator vector.1 :=
  rfl

/-- Self-adjointness descends to the invariant kernel complement. -/
theorem selfAdjointKernelComplementOperator_isSelfAdjoint
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) :
    IsSelfAdjoint
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner Real (operator first.1) second.1 =
    inner Real first.1 (operator second.1)
  exact hSelfAdjoint.isSymmetric first.1 second.1

/-- The irreducible analytic input on the actual zero-mode-free space. -/
structure SelfAdjointKernelComplementGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) : Prop where
  kernel_finite : FiniteDimensional Real operator.ker
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ vector : SelfAdjointKernelComplement operator,
    gap * ‖vector‖ ≤
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖

/-- Reciprocal gap in the form used by the global lower-bound theorem. -/
def SelfAdjointKernelComplementGapData.inverseGapConstant
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) : NNReal :=
  ⟨data.gap⁻¹, inv_nonneg.mpr (le_of_lt data.gap_pos)⟩

/-- Convert the coercive estimate to `‖x‖ ≤ gap⁻¹ ‖H_red x‖`. -/
theorem selfAdjointKernelComplement_globalLowerBound
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (vector : SelfAdjointKernelComplement operator) :
    ‖vector‖ ≤
      (data.inverseGapConstant : Real) *
        ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
  have hLower := data.lowerBound vector
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  change ‖vector‖ ≤ data.gap⁻¹ *
    ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖
  calc
    ‖vector‖ = data.gap⁻¹ * (data.gap * ‖vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ *
        ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- The restricted operator is injective. -/
theorem selfAdjointKernelComplementOperator_injective
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    Function.Injective
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) := by
  intro first second hEqual
  have hZero :
      selfAdjointKernelComplementOperator operator hSelfAdjoint
          (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hLower := data.lowerBound (first - second)
  rw [hZero, norm_zero] at hLower
  have hNorm : ‖first - second‖ = 0 := by
    by_contra hNonzero
    have hNormPos : 0 < ‖first - second‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNonzero)
    have hProductPos : 0 < data.gap * ‖first - second‖ :=
      mul_pos data.gap_pos hNormPos
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Self-adjointness upgrades the lower bound to surjectivity on the actual
kernel complement. -/
theorem selfAdjointKernelComplementOperator_surjective
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    Function.Surjective
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) :=
  selfAdjoint_surjective_of_globalLowerBound
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    (selfAdjointKernelComplementOperator_isSelfAdjoint operator hSelfAdjoint)
    data.inverseGapConstant
    (selfAdjointKernelComplement_globalLowerBound operator hSelfAdjoint data)

/-- The range of the original operator is exactly the orthogonal complement of
its actual kernel. -/
theorem selfAdjoint_operator_range_eq_kernelComplement
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    operator.range = operator.kerᗮ := by
  apply le_antisymm
  · intro target hTarget
    obtain ⟨source, rfl⟩ := hTarget
    rw [Submodule.mem_orthogonal']
    intro zeroMode hZeroMode
    have hKernel : operator zeroMode = 0 :=
      LinearMap.mem_ker.mp hZeroMode
    calc
      inner Real (operator source) zeroMode =
          inner Real source (operator zeroMode) :=
        hSelfAdjoint.isSymmetric source zeroMode
      _ = 0 := by rw [hKernel, inner_zero_right]
  · intro target hTarget
    let reducedTarget : SelfAdjointKernelComplement operator :=
      ⟨target, hTarget⟩
    obtain ⟨source, hSource⟩ :=
      selfAdjointKernelComplementOperator_surjective operator hSelfAdjoint data
        reducedTarget
    exact ⟨source.1, congrArg Subtype.val hSource⟩

/-- Closed range is now a theorem, not an extra Fredholm premise. -/
theorem selfAdjoint_operator_range_closed
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    IsClosed (operator.range : Set E) := by
  rw [selfAdjoint_operator_range_eq_kernelComplement operator hSelfAdjoint data]
  exact operator.kerᗮ.isClosed

/-- The genuine bounded self-adjoint operator is Fredholm once its actual
kernel is finite and it has a gap on the kernel complement. -/
theorem selfAdjoint_fredholm_of_kernelComplementGap
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    IsClosed (operator.range : Set E) ∧
      FiniteDimensional Real operator.ker ∧
      FiniteDimensional Real (E ⧸ operator.range) := by
  letI : FiniteDimensional Real operator.ker := data.kernel_finite
  exact boundedSelfAdjoint_fredholm_of_closedRange_finiteKernel operator
    hSelfAdjoint
    (selfAdjoint_operator_range_closed operator hSelfAdjoint data)
    data.kernel_finite

/-- The corresponding Fredholm index is zero. -/
theorem selfAdjoint_index_zero_of_kernelComplementGap
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    operator.toLinearMap.index = 0 := by
  letI : FiniteDimensional Real operator.ker := data.kernel_finite
  exact boundedSelfAdjoint_index_zero operator hSelfAdjoint
    (selfAdjoint_operator_range_closed operator hSelfAdjoint data)
    data.kernel_finite

/-- Continuous equivalence defined by the reduced Hessian. -/
noncomputable def selfAdjointKernelComplementEquiv
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplement operator ≃L[Real]
      SelfAdjointKernelComplement operator :=
  ContinuousLinearEquiv.ofBijective
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    ⟨selfAdjointKernelComplementOperator_injective operator hSelfAdjoint data,
      selfAdjointKernelComplementOperator_surjective operator hSelfAdjoint data⟩

/-- Canonical Green operator after removing the true zero modes. -/
noncomputable def selfAdjointKernelComplementGreen
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  (selfAdjointKernelComplementEquiv operator hSelfAdjoint data).symm

@[simp]
theorem selfAdjointKernelComplementOperator_green
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementOperator operator hSelfAdjoint
        (selfAdjointKernelComplementGreen operator hSelfAdjoint data vector) =
      vector :=
  (selfAdjointKernelComplementEquiv operator hSelfAdjoint data).apply_symm_apply
    vector

@[simp]
theorem selfAdjointKernelComplementGreen_operator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementGreen operator hSelfAdjoint data
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector) =
      vector :=
  (selfAdjointKernelComplementEquiv operator hSelfAdjoint data).symm_apply_apply
    vector

/-- Pointwise Green estimate. -/
theorem selfAdjointKernelComplementGreen_norm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (vector : SelfAdjointKernelComplement operator) :
    ‖selfAdjointKernelComplementGreen operator hSelfAdjoint data vector‖ ≤
      data.gap⁻¹ * ‖vector‖ := by
  let preimage :=
    selfAdjointKernelComplementGreen operator hSelfAdjoint data vector
  have hLower := data.lowerBound preimage
  rw [selfAdjointKernelComplementOperator_green operator hSelfAdjoint data
      vector] at hLower
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  calc
    ‖preimage‖ = data.gap⁻¹ * (data.gap * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- Operator-norm control of the canonical reduced Green operator. -/
theorem selfAdjointKernelComplementGreen_opNorm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    ‖selfAdjointKernelComplementGreen operator hSelfAdjoint data‖ ≤
      data.gap⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr (le_of_lt data.gap_pos))
  intro vector
  exact selfAdjointKernelComplementGreen_norm_le operator hSelfAdjoint data
    vector

/-- Terminal generic certificate on the actual zero-mode complement. -/
structure SelfAdjointKernelComplementCertificate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) : Prop where
  range_eq_kernelComplement : operator.range = operator.kerᗮ
  range_closed : IsClosed (operator.range : Set E)
  fredholm :
    IsClosed (operator.range : Set E) ∧
      FiniteDimensional Real operator.ker ∧
      FiniteDimensional Real (E ⧸ operator.range)
  index_zero : operator.toLinearMap.index = 0
  reduced_injective : Function.Injective
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
  reduced_surjective : Function.Surjective
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
  green_leftInverse : Function.LeftInverse
    (selfAdjointKernelComplementGreen operator hSelfAdjoint data)
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
  green_rightInverse : Function.RightInverse
    (selfAdjointKernelComplementGreen operator hSelfAdjoint data)
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
  green_opNorm_le :
    ‖selfAdjointKernelComplementGreen operator hSelfAdjoint data‖ ≤ data.gap⁻¹

/-- Construction of the terminal generic certificate. -/
def selfAdjointKernelComplementCertificate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementCertificate operator hSelfAdjoint data where
  range_eq_kernelComplement :=
    selfAdjoint_operator_range_eq_kernelComplement operator hSelfAdjoint data
  range_closed :=
    selfAdjoint_operator_range_closed operator hSelfAdjoint data
  fredholm :=
    selfAdjoint_fredholm_of_kernelComplementGap operator hSelfAdjoint data
  index_zero :=
    selfAdjoint_index_zero_of_kernelComplementGap operator hSelfAdjoint data
  reduced_injective :=
    selfAdjointKernelComplementOperator_injective operator hSelfAdjoint data
  reduced_surjective :=
    selfAdjointKernelComplementOperator_surjective operator hSelfAdjoint data
  green_leftInverse :=
    selfAdjointKernelComplementGreen_operator operator hSelfAdjoint data
  green_rightInverse :=
    selfAdjointKernelComplementOperator_green operator hSelfAdjoint data
  green_opNorm_le :=
    selfAdjointKernelComplementGreen_opNorm_le operator hSelfAdjoint data

/-- Public checkpoint: finite actual kernel plus a gap on its orthogonal
complement gives the whole reduced Fredholm/Green package. -/
theorem self_adjoint_actual_kernel_complement_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementCertificate operator hSelfAdjoint data :=
  selfAdjointKernelComplementCertificate operator hSelfAdjoint data

end
end P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
end JanusFormal
