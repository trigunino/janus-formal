import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Actual-kernel complement trivialization over an arbitrary parameter base

For `H : Base → End(E)`, one anchor `b0` fixes the model reduced Hilbert space
`(ker H_b0)ᗮ`. Certified unitary transports carry that space to every genuine
current complement. The actual restricted Hessians are then conjugated back to
the one fixed anchor space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyTrivialization4D

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 2800000
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {Base E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

private abbrev ReducedFiber
    (operator : Base → E →L[Real] E) (base : Base) :=
  SelfAdjointKernelComplement (operator base)

/-- Unitary trivialization of the genuine kernel-complement family from one
chosen anchor base point. -/
structure SelfAdjointKernelComplementBaseFamilyTrivializationData
    (operator : Base → E →L[Real] E)
    (hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base))
    (anchor : Base) where
  transport : ∀ base,
    ReducedFiber operator anchor ≃L[Real] ReducedFiber operator base
  transport_inner : ∀ base first second,
    inner Real (transport base first) (transport base second) =
      inner Real first second
  transport_norm : ∀ base vector,
    ‖transport base vector‖ = ‖vector‖
  transport_anchor : transport anchor = ContinuousLinearEquiv.refl Real _

namespace SelfAdjointKernelComplementBaseFamilyTrivializationData

/-- The actual Hessian restricted to the current genuine kernel complement. -/
def currentReducedOperator
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (_data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) :
    ReducedFiber operator base →L[Real] ReducedFiber operator base :=
  selfAdjointKernelComplementOperator (operator base) (hSelfAdjoint base)

/-- Conjugate the genuine current reduced operator to the anchor complement. -/
def transportedReducedOperator
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) :
    ReducedFiber operator anchor →L[Real] ReducedFiber operator anchor :=
  (data.transport base).symm.toContinuousLinearMap.comp
    ((data.currentReducedOperator base).comp
      (data.transport base).toContinuousLinearMap)

@[simp]
theorem transportedReducedOperator_apply
    {operator : Base → E →L[Real] E}
    {hSelfAdjoint : ∀ base, IsSelfAdjoint (operator base)}
    {anchor : Base}
    (data : SelfAdjointKernelComplementBaseFamilyTrivializationData
      operator hSelfAdjoint anchor)
    (base : Base) (vector : ReducedFiber operator anchor) :
    data.transportedReducedOperator base vector =
      (data.transport base).symm
        (data.currentReducedOperator base (data.transport base vector)) :=
  rfl

end SelfAdjointKernelComplementBaseFamilyTrivializationData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementBaseFamilyTrivialization4D
end JanusFormal
