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

/-- The canonical identification of the two zero-fibre complements. -/
private def zeroKernelComplementEquiv
    {first second : Real → E →L[Real] E}
    (hZero : first 0 = second 0) :
    (first 0).kerᗮ ≃ₗᵢ[Real] (second 0).kerᗮ where
  toFun := fun vector =>
    ⟨vector.1, by rw [← hZero]; exact vector.2⟩
  invFun := fun vector =>
    ⟨vector.1, by rw [hZero]; exact vector.2⟩
  left_inv := by intro vector; rfl
  right_inv := by intro vector; rfl
  map_add' := by intro firstVector secondVector; rfl
  map_smul' := by intro scalar vector; rfl
  norm_map' := by intro vector; rfl

/-- Conjugation of a zero-fibre operator by the canonical identification. -/
private def transportZeroGreen
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0) :
    (first 0).kerᗮ →L[Real] (first 0).kerᗮ :=
  let equivalence := zeroKernelComplementEquiv hZero
  equivalence.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (data.green.comp
      equivalence.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem transportZeroGreen_opNorm
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0) :
    ‖transportZeroGreen data hZero‖ = ‖data.green‖ := by
  let equivalence := zeroKernelComplementEquiv hZero
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg data.green)
    intro vector
    change ‖equivalence.symm (data.green (equivalence vector))‖ ≤
      ‖data.green‖ * ‖vector‖
    rw [equivalence.symm.norm_map]
    simpa only [equivalence.norm_map] using
      data.green.le_opNorm (equivalence vector)
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (transportZeroGreen data hZero))
    intro vector
    have hBound := (transportZeroGreen data hZero).le_opNorm
      (equivalence.symm vector)
    change ‖data.green vector‖ ≤
      ‖transportZeroGreen data hZero‖ * ‖vector‖
    simpa [transportZeroGreen, equivalence] using hBound

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
    (transportZero data hZero).gap = data.gap :=
  rfl

end FiniteKernelComplementBasepointNormGapData

namespace FiniteKernelComplementBasepointGreenData

/-- Reinterpret a basepoint Green packet through equality of the two operators
at zero. -/
def transportZero
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0) :
    FiniteKernelComplementBasepointGreenData first := by
  let equivalence := zeroKernelComplementEquiv hZero
  let operatorMem : ∀ vector : (first 0).kerᗮ,
      first 0 vector.1 ∈ (first 0).kerᗮ := by
    intro vector
    have hMem := data.operator_mem_complement (equivalence vector)
    change second 0 vector.1 ∈ (second 0).kerᗮ at hMem
    rw [← hZero] at hMem
    exact hMem
  exact {
    operator_mem_complement := operatorMem
    green := transportZeroGreen data hZero
    operator_green := by
      intro vector
      unfold transportZeroGreen
      change first 0 (equivalence.symm (data.green (equivalence vector))).1 = vector.1
      calc
        first 0 (equivalence.symm (data.green (equivalence vector))).1 =
            second 0 (data.green (equivalence vector)).1 :=
          congrArg (fun map => map (data.green (equivalence vector)).1) hZero
        _ = (equivalence vector).1 := data.operator_green (equivalence vector)
        _ = vector.1 := rfl
    green_operator := by
      intro vector
      apply Subtype.ext
      unfold transportZeroGreen
      change (equivalence.symm
        (data.green (equivalence ⟨first 0 vector.1, operatorMem vector⟩))).1 = vector.1
      have hInput : equivalence ⟨first 0 vector.1, operatorMem vector⟩ =
          ⟨second 0 (equivalence vector).1,
            data.operator_mem_complement (equivalence vector)⟩ := by
        apply Subtype.ext
        exact congrArg (fun map => map vector.1) hZero
      rw [hInput, data.green_operator]
      rfl
  }

@[simp]
theorem transportZero_green_opNorm
    {first second : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0) :
    ‖(transportZero data hZero).green‖ = ‖data.green‖ := by
  exact transportZeroGreen_opNorm data hZero

end FiniteKernelComplementBasepointGreenData

/-- A Green bound by the inverse gap is invariant under zero-fibre transport. -/
theorem transportZero_green_norm_le_gap_inv
    {first second : Real → E →L[Real] E}
    (gap : FiniteKernelComplementBasepointNormGapData second)
    (green : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0)
    (hBound : ‖green.green‖ ≤ gap.gap⁻¹) :
    ‖(FiniteKernelComplementBasepointGreenData.transportZero green hZero).green‖ ≤
      (FiniteKernelComplementBasepointNormGapData.transportZero gap hZero).gap⁻¹ := by
  simpa using hBound

/-- Public zero-fibre transport checkpoint. -/
theorem finite_kernel_complement_basepoint_data_transport_gate
    {first second : Real → E →L[Real] E}
    (gap : FiniteKernelComplementBasepointNormGapData second)
    (green : FiniteKernelComplementBasepointGreenData second)
    (hZero : first 0 = second 0)
    (hBound : ‖green.green‖ ≤ gap.gap⁻¹) :
    (FiniteKernelComplementBasepointNormGapData.transportZero gap hZero).gap = gap.gap ∧
    ‖(FiniteKernelComplementBasepointGreenData.transportZero green hZero).green‖ = ‖green.green‖ ∧
    ‖(FiniteKernelComplementBasepointGreenData.transportZero green hZero).green‖ ≤
      (FiniteKernelComplementBasepointNormGapData.transportZero gap hZero).gap⁻¹ :=
  ⟨rfl, FiniteKernelComplementBasepointGreenData.transportZero_green_opNorm green hZero,
    transportZero_green_norm_le_gap_inv gap green hZero hBound⟩

end
end P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D
end JanusFormal
