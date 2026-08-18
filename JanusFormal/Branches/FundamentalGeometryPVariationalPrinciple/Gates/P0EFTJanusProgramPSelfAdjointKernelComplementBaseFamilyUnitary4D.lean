import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyTrivialization4D

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyUnitary4D

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 2800000
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyTrivialization4D

variable {Base E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

private abbrev ReducedFiber
    (operator : Base → E →L[Real] E) (base : Base) :=
  SelfAdjointKernelComplement (operator base)

namespace SelfAdjointKernelComplementBaseFamilyTrivializationData

/-- Inverse transport preserves norm. -/
theorem transport_symm_norm
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) (vector : ReducedFiber operator base) :
    ‖(data.transport base).symm vector‖ = ‖vector‖ := by
  have hNorm := data.transport_norm base ((data.transport base).symm vector)
  rw [(data.transport base).apply_symm_apply vector] at hNorm
  exact hNorm.symm

/-- Unitary conjugation preserves self-adjointness. -/
theorem transportedReducedOperator_isSelfAdjoint
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) :
    IsSelfAdjoint (data.transportedReducedOperator base) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  let transport := data.transport base
  let reduced := data.currentReducedOperator base
  calc
    inner Real (data.transportedReducedOperator base first) second =
        inner Real
          (transport (transport.symm (reduced (transport first))))
          (transport second) := by
      exact (data.transport_inner base
        (transport.symm (reduced (transport first))) second).symm
    _ = inner Real (reduced (transport first)) (transport second) := by
      rw [transport.apply_symm_apply]
    _ = inner Real (transport first) (reduced (transport second)) := by
      exact
        (selfAdjointKernelComplementOperator_isSelfAdjoint
          (operator base) (hSelfAdjoint base)).isSymmetric
            (transport first) (transport second)
    _ = inner Real first
        (transport.symm (reduced (transport second))) := by
      calc
        _ = inner Real (transport first)
            (transport (transport.symm (reduced (transport second)))) := by
          rw [transport.apply_symm_apply]
        _ = _ := data.transport_inner base first
          (transport.symm (reduced (transport second)))
    _ = inner Real first
        (data.transportedReducedOperator base second) := rfl

/-- At the anchor the transported family is the ordinary genuine reduced
operator. -/
theorem transportedReducedOperator_anchor
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor) :
    data.transportedReducedOperator anchor = data.currentReducedOperator anchor := by
  unfold SelfAdjointKernelComplementBaseFamilyTrivializationData.transportedReducedOperator
  rw [data.transport_anchor]
  ext vector
  rfl

/-- Public unitary-transport checkpoint. -/
theorem self_adjoint_kernel_complement_base_family_unitary_gate
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor) :
    (∀ base, IsSelfAdjoint (data.transportedReducedOperator base)) ∧
    data.transportedReducedOperator anchor = data.currentReducedOperator anchor :=
  ⟨transportedReducedOperator_isSelfAdjoint data,
    transportedReducedOperator_anchor data⟩

end SelfAdjointKernelComplementBaseFamilyTrivializationData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyUnitary4D
end JanusFormal
