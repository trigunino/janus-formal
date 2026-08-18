import Mathlib.Analysis.Calculus.FDeriv.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D

/-!
# Differentiable trivializations of varying kernel complements

The existing unitary trivialization transports the genuine fibres
`(ker H_0)ᗮ -> (ker H_a)ᗮ`, but it carries no regularity in the parameter.
For geometric determinant-line families we record C1 regularity after coercing
the transported vector back to the common ambient Hilbert space.

This avoids differentiating a function with a parameter-dependent subtype as
codomain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableKernelComplementTrivialization4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- C1 regularity of an already certified unitary kernel-complement
trivialization. -/
structure DifferentiableKernelComplementTrivializationData
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (trivialization : SelfAdjointKernelComplementFamilyTrivializationData
      operator hSelfAdjoint) : Prop where
  transport_differentiable : ∀
      (vector : SelfAdjointKernelComplement (operator 0)),
    Differentiable Real
      (fun parameter : Real =>
        ((trivialization.transport parameter vector :
            SelfAdjointKernelComplement (operator parameter)) : E))

namespace DifferentiableKernelComplementTrivializationData

/-- Every transported reduced vector is continuous in the common ambient
Hilbert space. -/
theorem transport_continuous
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    {trivialization : SelfAdjointKernelComplementFamilyTrivializationData
      operator hSelfAdjoint}
    (data : DifferentiableKernelComplementTrivializationData trivialization)
    (vector : SelfAdjointKernelComplement (operator 0)) :
    Continuous
      (fun parameter : Real =>
        ((trivialization.transport parameter vector :
            SelfAdjointKernelComplement (operator parameter)) : E)) :=
  (data.transport_differentiable vector).continuous

/-- The C1 upgrade retains the exact basepoint identity. -/
theorem transport_zero
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    {trivialization : SelfAdjointKernelComplementFamilyTrivializationData
      operator hSelfAdjoint}
    (_data : DifferentiableKernelComplementTrivializationData trivialization) :
    trivialization.transport 0 = ContinuousLinearEquiv.refl Real _ :=
  trivialization.transport_zero

/-- The C1 upgrade retains exact unitarity. -/
theorem transport_norm
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    {trivialization : SelfAdjointKernelComplementFamilyTrivializationData
      operator hSelfAdjoint}
    (_data : DifferentiableKernelComplementTrivializationData trivialization)
    (parameter : Real)
    (vector : SelfAdjointKernelComplement (operator 0)) :
    ‖trivialization.transport parameter vector‖ = ‖vector‖ :=
  trivialization.transport_norm parameter vector

/-- Public differentiable complement-trivialization checkpoint. -/
theorem differentiable_kernel_complement_trivialization_gate
    {operator : Real → E →L[Real] E}
    {hSelfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)}
    (trivialization : SelfAdjointKernelComplementFamilyTrivializationData
      operator hSelfAdjoint)
    (data : DifferentiableKernelComplementTrivializationData trivialization) :
    (∀ vector : SelfAdjointKernelComplement (operator 0),
      Differentiable Real
        (fun parameter : Real =>
          ((trivialization.transport parameter vector :
              SelfAdjointKernelComplement (operator parameter)) : E))) ∧
    (∀ vector : SelfAdjointKernelComplement (operator 0),
      Continuous
        (fun parameter : Real =>
          ((trivialization.transport parameter vector :
              SelfAdjointKernelComplement (operator parameter)) : E))) ∧
    trivialization.transport 0 = ContinuousLinearEquiv.refl Real _ :=
  ⟨data.transport_differentiable,
    data.transport_continuous,
    data.transport_zero⟩

end DifferentiableKernelComplementTrivializationData

end
end P0EFTJanusProgramPDifferentiableKernelComplementTrivialization4D
end JanusFormal
