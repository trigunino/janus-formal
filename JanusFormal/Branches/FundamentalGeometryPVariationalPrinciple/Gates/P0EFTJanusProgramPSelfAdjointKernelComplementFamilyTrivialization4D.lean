import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointUniformGapFamily4D

/-!
# Unitary trivialization of varying actual-kernel complements

For a parameter family `H_a`, the spaces `(ker H_a)ᗮ` need not be
definitionally equal.  A determinant connection must therefore either work in
a Hilbert bundle or choose a certified unitary trivialization.

This file implements the second route.  One continuous linear equivalence

`T_a : (ker H_0)ᗮ ≃ (ker H_a)ᗮ`

transports every reduced Hessian back to the fixed base complement.  The
transported family is self-adjoint, and a uniform lower bound on the original
fibres becomes a uniform gap on the fixed Hilbert space.  Hence the generic
Green-family and Bismut--Freed constructions apply without pretending that the
varying subtypes are definitionally identical.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointUniformGapFamily4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

private abbrev ReducedFiber
    (operator : Real → E →L[Real] E) (parameter : Real) :=
  SelfAdjointKernelComplement (operator parameter)

/-- Unitary trivialization of the genuine kernel-complement family. -/
structure SelfAdjointKernelComplementFamilyTrivializationData
    (operator : Real → E →L[Real] E)
    (hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)) where
  transport : ∀ parameter,
    ReducedFiber operator 0 ≃L[Real] ReducedFiber operator parameter
  transport_inner : ∀ parameter first second,
    inner Real (transport parameter first) (transport parameter second) =
      inner Real first second
  transport_norm : ∀ parameter vector,
    ‖transport parameter vector‖ = ‖vector‖
  transport_zero : transport 0 = ContinuousLinearEquiv.refl Real _

namespace SelfAdjointKernelComplementFamilyTrivializationData

/-- The reduced operator on the current fibre. -/
def currentReducedOperator
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (_data : SelfAdjointKernelComplementFamilyTrivializationData operator
      hSelfAdjoint)
    (parameter : Real) :
    ReducedFiber operator parameter →L[Real] ReducedFiber operator parameter :=
  selfAdjointKernelComplementOperator (operator parameter)
    (hSelfAdjoint parameter)

/-- Transport the current reduced operator to the fixed base complement. -/
def transportedReducedOperator
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementFamilyTrivializationData operator
      hSelfAdjoint)
    (parameter : Real) :
    ReducedFiber operator 0 →L[Real] ReducedFiber operator 0 :=
  (data.transport parameter).symm.toContinuousLinearMap.comp
    ((data.currentReducedOperator parameter).comp
      (data.transport parameter).toContinuousLinearMap)

@[simp]
theorem transportedReducedOperator_apply
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementFamilyTrivializationData operator
      hSelfAdjoint)
    (parameter : Real) (vector : ReducedFiber operator 0) :
    data.transportedReducedOperator parameter vector =
      (data.transport parameter).symm
        (data.currentReducedOperator parameter
          (data.transport parameter vector)) :=
  rfl

/-- The inverse transport preserves norm as well. -/
theorem transport_symm_norm
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementFamilyTrivializationData operator
      hSelfAdjoint)
    (parameter : Real) (vector : ReducedFiber operator parameter) :
    ‖(data.transport parameter).symm vector‖ = ‖vector‖ := by
  have hNorm := data.transport_norm parameter
    ((data.transport parameter).symm vector)
  rw [(data.transport parameter).apply_symm_apply vector] at hNorm
  exact hNorm.symm

/-- Unitary conjugation preserves self-adjointness. -/
theorem transportedReducedOperator_isSelfAdjoint
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementFamilyTrivializationData operator
      hSelfAdjoint)
    (parameter : Real) :
    IsSelfAdjoint (data.transportedReducedOperator parameter) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  let transport := data.transport parameter
  let reduced := data.currentReducedOperator parameter
  calc
    inner Real (data.transportedReducedOperator parameter first) second =
        inner Real
          (transport (transport.symm (reduced (transport first))))
          (transport second) := by
      exact (data.transport_inner parameter
        (transport.symm (reduced (transport first))) second).symm
    _ = inner Real (reduced (transport first)) (transport second) := by
      rw [transport.apply_symm_apply]
    _ = inner Real (transport first) (reduced (transport second)) := by
      exact
        (selfAdjointKernelComplementOperator_isSelfAdjoint
          (operator parameter) (hSelfAdjoint parameter)).isSymmetric
            (transport first) (transport second)
    _ = inner Real first
        (transport.symm (reduced (transport second))) := by
      have hInner := data.transport_inner parameter first
        (transport.symm (reduced (transport second)))
      rw [transport.apply_symm_apply] at hInner
      exact hInner
    _ = inner Real first
        (data.transportedReducedOperator parameter second) :=
      rfl

/-- At the base parameter the transported family is the ordinary reduced
operator. -/
theorem transportedReducedOperator_zero
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementFamilyTrivializationData operator
      hSelfAdjoint) :
    data.transportedReducedOperator 0 = data.currentReducedOperator 0 := by
  rw [transportedReducedOperator, data.transport_zero]
  ext vector
  rfl

end SelfAdjointKernelComplementFamilyTrivializationData

/-- A unitary kernel-complement trivialization together with one positive lower
bound on every current reduced fibre. -/
structure SelfAdjointKernelComplementUniformGapTrivializationData
    (operator : Real → E →L[Real] E)
    (hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)) where
  trivialization :
    SelfAdjointKernelComplementFamilyTrivializationData operator hSelfAdjoint
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ parameter
    (vector : ReducedFiber operator parameter),
    gap * ‖vector‖ ≤
      ‖trivialization.currentReducedOperator parameter vector‖

namespace SelfAdjointKernelComplementUniformGapTrivializationData

/-- The transported family on the fixed base complement. -/
def fixedOperator
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementUniformGapTrivializationData operator
      hSelfAdjoint) :
    Real → ReducedFiber operator 0 →L[Real] ReducedFiber operator 0 :=
  data.trivialization.transportedReducedOperator

/-- The original fibrewise bound is unchanged by the unitary transport. -/
def toUniformGapFamily
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementUniformGapTrivializationData operator
      hSelfAdjoint) :
    SelfAdjointUniformGapFamilyData data.fixedOperator where
  selfAdjoint := data.trivialization.transportedReducedOperator_isSelfAdjoint
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := by
    intro parameter vector
    have hCurrent := data.lowerBound parameter
      (data.trivialization.transport parameter vector)
    calc
      data.gap * ‖vector‖ =
          data.gap * ‖data.trivialization.transport parameter vector‖ := by
        rw [data.trivialization.transport_norm parameter vector]
      _ ≤ ‖data.trivialization.currentReducedOperator parameter
          (data.trivialization.transport parameter vector)‖ := hCurrent
      _ = ‖data.fixedOperator parameter vector‖ := by
        symm
        exact data.trivialization.transport_symm_norm parameter
          (data.trivialization.currentReducedOperator parameter
            (data.trivialization.transport parameter vector))

/-- Canonical Green family after fixing the base complement. -/
noncomputable def fixedGreen
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (data : SelfAdjointKernelComplementUniformGapTrivializationData operator
      hSelfAdjoint)
    (parameter : Real) :
    ReducedFiber operator 0 →L[Real] ReducedFiber operator 0 :=
  data.toUniformGapFamily.green parameter

/-- Public kernel-complement trivialization checkpoint. -/
theorem self_adjoint_kernel_complement_family_trivialization_gate
    (operator : Real → E →L[Real] E)
    (hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter))
    (data : SelfAdjointKernelComplementUniformGapTrivializationData operator
      hSelfAdjoint) :
    (∀ parameter,
      IsSelfAdjoint (data.fixedOperator parameter)) ∧
      (∀ parameter vector,
        data.gap * ‖vector‖ ≤ ‖data.fixedOperator parameter vector‖) ∧
      (∀ parameter vector,
        data.fixedOperator parameter (data.fixedGreen parameter vector) =
          vector) ∧
      (∀ parameter,
        ‖data.fixedGreen parameter‖ ≤ data.gap⁻¹) :=
  ⟨data.toUniformGapFamily.selfAdjoint,
    data.toUniformGapFamily.lowerBound,
    data.toUniformGapFamily.operator_green,
    data.toUniformGapFamily.green_opNorm_le⟩

end SelfAdjointKernelComplementUniformGapTrivializationData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
end JanusFormal
