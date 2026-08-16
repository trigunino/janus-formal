import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyUnitary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D

/-!
# Uniform gap on the genuine kernel-complement family over a general base

A positive lower bound is imposed on the actual current reduced fibers, not on
an independently supplied fixed-space operator.  Unitary transport then creates
the fixed operator family and its canonical Green inverse.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementBaseUniformGap4D

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 2800000
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyTrivialization4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyUnitary4D
open P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D

variable {Base E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

private abbrev ReducedFiber
    (operator : Base → E →L[Real] E) (base : Base) :=
  SelfAdjointKernelComplement (operator base)

/-- Genuine current-fiber gap plus one unitary trivialization from the anchor. -/
structure SelfAdjointKernelComplementBaseUniformGapTrivializationData
    (operator : Base → E →L[Real] E)
    (hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base))
    (anchor : Base) where
  trivialization : SelfAdjointKernelComplementBaseFamilyTrivializationData
    operator hSelfAdjoint anchor
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ base (vector : ReducedFiber operator base),
    gap * ‖vector‖ ≤
      ‖trivialization.currentReducedOperator base vector‖

namespace SelfAdjointKernelComplementBaseUniformGapTrivializationData

/-- Genuine reduced family transported to the fixed anchor complement. -/
def fixedOperator
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor) :
    Base → ReducedFiber operator anchor →L[Real] ReducedFiber operator anchor :=
  data.trivialization.transportedReducedOperator

/-- The fiberwise gap is unchanged after unitary transport. -/
def toUniformGapBaseFamily
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor) :
    SelfAdjointUniformGapBaseFamilyData data.fixedOperator where
  selfAdjoint := data.trivialization.transportedReducedOperator_isSelfAdjoint
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := by
    intro base vector
    have hCurrent := data.lowerBound base (data.trivialization.transport base vector)
    calc
      data.gap * ‖vector‖ =
          data.gap * ‖data.trivialization.transport base vector‖ := by
        rw [data.trivialization.transport_norm base vector]
      _ ≤ ‖data.trivialization.currentReducedOperator base
          (data.trivialization.transport base vector)‖ := hCurrent
      _ = ‖data.fixedOperator base vector‖ := by
        symm
        exact data.trivialization.transport_symm_norm base
          (data.trivialization.currentReducedOperator base
            (data.trivialization.transport base vector))

/-- Canonical Green family on the fixed anchor complement. -/
noncomputable def fixedGreen
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) :
    ReducedFiber operator anchor →L[Real] ReducedFiber operator anchor :=
  data.toUniformGapBaseFamily.green base

@[simp]
theorem fixedOperator_fixedGreen
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) (vector : ReducedFiber operator anchor) :
    data.fixedOperator base (data.fixedGreen base vector) = vector :=
  data.toUniformGapBaseFamily.operator_green base vector

@[simp]
theorem fixedGreen_fixedOperator
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) (vector : ReducedFiber operator anchor) :
    data.fixedGreen base (data.fixedOperator base vector) = vector :=
  data.toUniformGapBaseFamily.green_operator base vector

/-- Uniform inverse bound. -/
theorem fixedGreen_opNorm_le
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) :
    ‖data.fixedGreen base‖ ≤ data.gap⁻¹ :=
  data.toUniformGapBaseFamily.green_opNorm_le base

/-- Public arbitrary-base actual-kernel reduced Green checkpoint. -/
theorem self_adjoint_kernel_complement_base_uniform_gap_gate
    (operator : Base → E →L[Real] E)
    (hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base))
    (anchor : Base)
    (data : SelfAdjointKernelComplementBaseUniformGapTrivializationData
      operator hSelfAdjoint anchor) :
    (∀ base, IsSelfAdjoint (data.fixedOperator base)) ∧
    (∀ base vector,
      data.gap * ‖vector‖ ≤ ‖data.fixedOperator base vector‖) ∧
    (∀ base vector,
      data.fixedOperator base (data.fixedGreen base vector) = vector) ∧
    (∀ base, ‖data.fixedGreen base‖ ≤ data.gap⁻¹) :=
  ⟨data.toUniformGapBaseFamily.selfAdjoint,
    data.toUniformGapBaseFamily.lowerBound,
    data.fixedOperator_fixedGreen,
    data.fixedGreen_opNorm_le⟩

end SelfAdjointKernelComplementBaseUniformGapTrivializationData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementBaseUniformGap4D
end JanusFormal
