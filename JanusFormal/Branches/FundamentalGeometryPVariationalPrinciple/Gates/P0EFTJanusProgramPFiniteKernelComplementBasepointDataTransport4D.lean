import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

/-!
# Transport basepoint kernel-complement data across equality at parameter zero

The family-level unitary continuation consumes a gap and a two-sided Green
operator for `operator 0`.  Existing H12/H14 certificates often present the
same data using a definitionally different spelling of that basepoint operator.

This file gives the exact zero-fibre transport.  If

`first 0 = second 0`,

then basepoint gap and Green packets for `second` induce the corresponding
packets for `first`.  The scalar gap and the Green operator norm are preserved
exactly.  No comparison estimate or new inverse is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace FiniteKernelComplementBasepointNormGapData

/-- Reinterpret a basepoint gap through equality of the two operators at zero. -/
def transportZero
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointNormGapData second)
    (hZero : first 0 = second 0) :
    FiniteKernelComplementBasepointNormGapData first where
  gap := data.gap
  gap_pos := data.gap_pos
  lower_bound := by
    intro vector hVector
    rw [hZero] at hVector ⊢
    exact data.lower_bound vector hVector

@[simp]
theorem transportZero_gap
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointNormGapData second)
    (hZero : first 0 = second 0) :
    (data.transportZero hZero).gap = data.gap :=
  rfl

end FiniteKernelComplementBasepointNormGapData

namespace FiniteKernelComplementBasepointGreenData

/-- Reinterpret a basepoint Green packet through equality of the two operators
at zero. -/
def transportZero
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0) :
    FiniteKernelComplementBasepointGreenData first where
  operator_mem_complement := by
    intro vector
    rw [hZero] at vector ⊢
    exact data.operator_mem_complement vector
  green := by
    rw [hZero]
    exact data.green
  operator_green := by
    intro vector
    rw [hZero] at vector ⊢
    exact data.operator_green vector
  green_operator := by
    intro vector
    rw [hZero] at vector ⊢
    exact data.green_operator vector

@[simp]
theorem transportZero_green_opNorm
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0) :
    ‖(data.transportZero hZero).green‖ = ‖data.green‖ := by
  cases hZero
  rfl

end FiniteKernelComplementBasepointGreenData

/-- A Green bound by the inverse gap is invariant under zero-fibre transport. -/
theorem transportZero_green_norm_le_gap_inv
    {first second : Real → E →L[Real] E}
    (gap : FiniteKernelComplementBasepointNormGapData second)
    (green : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0)
    (hBound : ‖green.green‖ ≤ gap.gap⁻¹) :
    ‖(green.transportZero hZero).green‖ ≤
      (gap.transportZero hZero).gap⁻¹ := by
  simpa using hBound

/-- Public zero-fibre transport checkpoint. -/
theorem finite_kernel_complement_basepoint_data_transport_gate
    {first second : Real → E →L[Real] E}
    (gap : FiniteKernelComplementBasepointNormGapData second)
    (green : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0)
    (hBound : ‖green.green‖ ≤ gap.gap⁻¹) :
    (gap.transportZero hZero).gap = gap.gap ∧
    ‖(green.transportZero hZero).green‖ = ‖green.green‖ ∧
    ‖(green.transportZero hZero).green‖ ≤
      (gap.transportZero hZero).gap⁻¹ :=
  ⟨rfl, green.transportZero_green_opNorm hZero,
    transportZero_green_norm_le_gap_inv gap green hZero hBound⟩

end
end P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D
end JanusFormal
