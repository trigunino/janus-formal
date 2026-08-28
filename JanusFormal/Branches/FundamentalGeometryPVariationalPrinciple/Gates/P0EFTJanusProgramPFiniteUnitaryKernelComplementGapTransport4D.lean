import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

/-!
# Transport a kernel-complement gap through a unitary frame

If an operator family is unitarily conjugate to its basepoint member, every
coercive norm estimate on the basepoint orthogonal kernel complement persists
with the same constant.  More precisely,

`gap * ‖x‖ ≤ ‖H_0 x‖`

for `x ∈ (ker H_0)ᗮ` implies

`gap * ‖y‖ ≤ ‖H_a y‖`

for `y ∈ (ker H_a)ᗮ`.

This is the direct spectral consequence of using one unitary Fredholm frame:
no second family gap or perturbative comparison is needed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A norm gap on the basepoint orthogonal complement. -/
structure FiniteKernelComplementBasepointNormGapData
    (operator : Real → E →L[Real] E) where
  gap : Real
  gap_pos : 0 < gap
  lower_bound : ∀ vector : E,
    vector ∈ (operator 0).kerᗮ →
      gap * ‖vector‖ ≤ ‖operator 0 vector‖

end
end P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D

namespace P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace FiniteUnitaryIntertwiningOperatorFrameData

/-- The basepoint norm gap persists at every parameter with the same constant. -/
theorem kernelComplement_norm_gap
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (gapData : FiniteKernelComplementBasepointNormGapData operator)
    (parameter : Real) (vector : E)
    (hVector : vector ∈ (operator parameter).kerᗮ) :
    gapData.gap * ‖vector‖ ≤ ‖operator parameter vector‖ := by
  let transport := frame.toFiniteUnitaryIntertwiningOperatorTransport
  let source : E := (transport.transport 0 parameter).symm vector
  have hSource : source ∈ (operator 0).kerᗮ :=
    transport.symm_transport_mem_kernel_orthogonal 0 parameter hVector
  have hNorm : ‖source‖ = ‖vector‖ := by
    exact (transport.transport 0 parameter).symm.norm_map vector
  have hLower := gapData.lower_bound source hSource
  have hOperator :
      transport.transport 0 parameter (operator 0 source) =
        operator parameter vector := by
    rw [← transport.intertwines 0 parameter source]
    exact congrArg (operator parameter)
      ((transport.transport 0 parameter).apply_symm_apply vector)
  calc
    gapData.gap * ‖vector‖ = gapData.gap * ‖source‖ := by rw [hNorm]
    _ ≤ ‖operator 0 source‖ := hLower
    _ = ‖transport.transport 0 parameter (operator 0 source)‖ := by
      rw [(transport.transport 0 parameter).norm_map]
    _ = ‖operator parameter vector‖ := by rw [hOperator]

/-- Equivalent subtype formulation on the canonical reduced fibre. -/
theorem kernelComplement_subtype_norm_gap
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (gapData : FiniteKernelComplementBasepointNormGapData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    gapData.gap * ‖vector‖ ≤ ‖operator parameter vector.1‖ :=
  kernelComplement_norm_gap frame gapData parameter vector.1 vector.2

/-- The transported gap gives injectivity of every operator on its orthogonal
kernel complement. -/
theorem kernelComplement_operator_injective
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (gapData : FiniteKernelComplementBasepointNormGapData operator)
    (parameter : Real) :
    Function.Injective
      (fun vector : (operator parameter).kerᗮ => operator parameter vector.1) := by
  intro first second hEqual
  apply Subtype.ext
  have hDifference :
      operator parameter (first.1 - second.1) = 0 := by
    change operator parameter first.1 = operator parameter second.1 at hEqual
    rw [map_sub, hEqual, sub_self]
  have hDifferenceMem :
      first.1 - second.1 ∈ (operator parameter).kerᗮ :=
    sub_mem first.2 second.2
  have hGap := kernelComplement_norm_gap frame gapData parameter
    (first.1 - second.1) hDifferenceMem
  rw [hDifference, norm_zero] at hGap
  have hNormZero : ‖first.1 - second.1‖ = 0 := by
    by_contra hNorm
    have hNormPos : 0 < ‖first.1 - second.1‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNorm)
    have hProductPos : 0 < gapData.gap * ‖first.1 - second.1‖ :=
      mul_pos gapData.gap_pos hNormPos
    exact (not_lt_of_ge hGap) hProductPos
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- Public unitary gap-transport checkpoint. -/
theorem finite_unitary_kernel_complement_gap_transport_gate
    (operator : Real → E →L[Real] E)
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (gapData : FiniteKernelComplementBasepointNormGapData operator) :
    (∀ parameter vector,
      vector ∈ (operator parameter).kerᗮ →
        gapData.gap * ‖vector‖ ≤ ‖operator parameter vector‖) ∧
    (∀ parameter,
      Function.Injective
        (fun vector : (operator parameter).kerᗮ =>
          operator parameter vector.1)) :=
  ⟨kernelComplement_norm_gap frame gapData,
    kernelComplement_operator_injective frame gapData⟩

end FiniteUnitaryIntertwiningOperatorFrameData

end
end P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
end JanusFormal
