import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# The actual-kernel gap from closed range

For a bounded self-adjoint operator, closed range gives the exact identity

`range H = (ker H)ᗮ`.

The restriction of `H` to `(ker H)ᗮ` is therefore a bounded bijection.  The
bounded inverse theorem supplies a quantitative lower bound, so the canonical
actual-kernel gap is not additional data once the classical H12 hypotheses
`range_closed` and `kernel_finite` are known.

This file turns those two hypotheses into
`SelfAdjointKernelComplementGapData`, and therefore into the reduced Green and
resolvent packages of the actual-kernel route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointClosedRangeKernelGap4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance closedRangeKernelComplementCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Closed range and self-adjointness identify the range with the actual
kernel complement. -/
theorem selfAdjoint_closedRange_range_eq_kernelComplement
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) :
    operator.range = operator.kerᗮ := by
  have hOrthogonal : operator.rangeᗮ = operator.ker := by
    rw [ContinuousLinearMap.orthogonal_range, hSelfAdjoint.adjoint_eq]
  calc
    operator.range = operator.range.topologicalClosure :=
      hClosed.submodule_topologicalClosure_eq.symm
    _ = operator.rangeᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure operator.range).symm
    _ = operator.kerᗮ := by rw [hOrthogonal]

/-- Injectivity of the restriction uses only that a vector cannot belong both
to `ker H` and to its orthogonal complement. -/
theorem selfAdjointKernelComplementOperator_injective_of_selfAdjoint
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) :
    Function.Injective
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) := by
  intro first second hEqual
  have hKernel : first.1 - second.1 ∈ operator.ker := by
    apply LinearMap.mem_ker.mpr
    change operator (first.1 - second.1) = 0
    rw [map_sub]
    exact congrArg Subtype.val hEqual |> sub_eq_zero.mpr
  have hOrthogonal :
      inner Real (first.1 - second.1) (first.1 - second.1) = 0 := by
    rw [inner_sub_right, first.2 (first.1 - second.1) hKernel,
      second.2 (first.1 - second.1) hKernel, sub_self]
  have hNorm : ‖first.1 - second.1‖ = 0 := by
    rw [← sq_eq_zero_iff, ← real_inner_self_eq_norm_sq]
    exact hOrthogonal
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- The restricted operator is surjective when the full range is closed. -/
theorem selfAdjointKernelComplementOperator_surjective_of_closedRange
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) :
    Function.Surjective
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) := by
  intro target
  have hRange : target.1 ∈ operator.range := by
    rw [selfAdjoint_closedRange_range_eq_kernelComplement operator hSelfAdjoint
      hClosed]
    exact target.2
  obtain ⟨source, hSource⟩ := hRange
  let orthogonalSource : SelfAdjointKernelComplement operator :=
    ⟨source - operator.ker.starProjection source, by
      exact operator.ker.sub_starProjection_mem_orthogonal source⟩
  refine ⟨orthogonalSource, ?_⟩
  apply Subtype.ext
  change operator (source - operator.ker.starProjection source) = target.1
  have hSource' : operator source = target.1 := hSource
  rw [map_sub, hSource']
  have hProjectionKernel :
      operator (operator.ker.starProjection source) = 0 := by
    apply LinearMap.mem_ker.mp
    exact operator.ker.starProjection_apply_mem source
  rw [hProjectionKernel, sub_zero]

/-- Continuous equivalence supplied by closed range. -/
noncomputable def selfAdjointClosedRangeKernelComplementEquiv
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) :
    SelfAdjointKernelComplement operator ≃L[Real]
      SelfAdjointKernelComplement operator :=
  ContinuousLinearEquiv.ofBijective
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    (LinearMap.ker_eq_bot.mpr
      (selfAdjointKernelComplementOperator_injective_of_selfAdjoint operator
        hSelfAdjoint))
    (LinearMap.range_eq_top.mpr
      (selfAdjointKernelComplementOperator_surjective_of_closedRange operator
        hSelfAdjoint hClosed))

/-- Bounded inverse obtained from the classical closed-range hypothesis. -/
noncomputable def selfAdjointClosedRangeKernelComplementInverse
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  (selfAdjointClosedRangeKernelComplementEquiv operator hSelfAdjoint
    hClosed).symm

/-- Positive control constant, including the zero-dimensional case. -/
def selfAdjointClosedRangeKernelComplementControl
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) : Real :=
  max 1
    ‖selfAdjointClosedRangeKernelComplementInverse operator hSelfAdjoint hClosed‖

/-- The canonical gap extracted from the bounded inverse. -/
def selfAdjointClosedRangeKernelComplementGap
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) : Real :=
  (selfAdjointClosedRangeKernelComplementControl operator hSelfAdjoint hClosed)⁻¹

theorem selfAdjointClosedRangeKernelComplementControl_pos
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) :
    0 < selfAdjointClosedRangeKernelComplementControl operator hSelfAdjoint
      hClosed := by
  unfold selfAdjointClosedRangeKernelComplementControl
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem selfAdjointClosedRangeKernelComplementGap_pos
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E)) :
    0 < selfAdjointClosedRangeKernelComplementGap operator hSelfAdjoint
      hClosed := by
  unfold selfAdjointClosedRangeKernelComplementGap
  exact inv_pos.mpr
    (selfAdjointClosedRangeKernelComplementControl_pos operator hSelfAdjoint
      hClosed)

/-- Lower bound obtained from the bounded inverse theorem. -/
theorem selfAdjointClosedRangeKernelComplement_lowerBound
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E))
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointClosedRangeKernelComplementGap operator hSelfAdjoint hClosed *
        ‖vector‖ ≤
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
  let inverse := selfAdjointClosedRangeKernelComplementInverse operator
    hSelfAdjoint hClosed
  let control := selfAdjointClosedRangeKernelComplementControl operator
    hSelfAdjoint hClosed
  have hInverse : inverse
      (selfAdjointKernelComplementOperator operator hSelfAdjoint vector) =
      vector :=
    (selfAdjointClosedRangeKernelComplementEquiv operator hSelfAdjoint
      hClosed).symm_apply_apply vector
  have hNorm : ‖vector‖ ≤ control *
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
    calc
      ‖vector‖ = ‖inverse
          (selfAdjointKernelComplementOperator operator hSelfAdjoint vector)‖ :=
        congrArg norm hInverse.symm
      _ ≤ ‖inverse‖ *
            ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ :=
        inverse.le_opNorm _
      _ ≤ control *
            ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ :=
        mul_le_mul_of_nonneg_right (le_max_right 1 ‖inverse‖)
          (norm_nonneg _)
  have hControlPos : 0 < control :=
    selfAdjointClosedRangeKernelComplementControl_pos operator hSelfAdjoint
      hClosed
  have hControlNe : control ≠ 0 := ne_of_gt hControlPos
  unfold selfAdjointClosedRangeKernelComplementGap
  change control⁻¹ * ‖vector‖ ≤ _
  calc
    control⁻¹ * ‖vector‖ ≤
        control⁻¹ *
          (control *
            ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖) :=
      mul_le_mul_of_nonneg_left hNorm
        (inv_nonneg.mpr (le_of_lt hControlPos))
    _ = ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ hControlNe, one_mul]

/-- Construct the actual-kernel gap from the classical H12 estimates. -/
def selfAdjointKernelComplementGapData_of_closedRange
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E))
    (hKernelFinite : FiniteDimensional Real operator.ker) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint where
  kernel_finite := hKernelFinite
  gap := selfAdjointClosedRangeKernelComplementGap operator hSelfAdjoint hClosed
  gap_pos := selfAdjointClosedRangeKernelComplementGap_pos operator hSelfAdjoint
    hClosed
  lowerBound := selfAdjointClosedRangeKernelComplement_lowerBound operator
    hSelfAdjoint hClosed

/-- Public bridge from the old H12 pair to the canonical actual-kernel gap. -/
def self_adjoint_closedRange_to_actualKernelGap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set E))
    (hKernelFinite : FiniteDimensional Real operator.ker) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  selfAdjointKernelComplementGapData_of_closedRange operator hSelfAdjoint hClosed
    hKernelFinite

end
end P0EFTJanusProgramPSelfAdjointClosedRangeKernelGap4D
end JanusFormal
