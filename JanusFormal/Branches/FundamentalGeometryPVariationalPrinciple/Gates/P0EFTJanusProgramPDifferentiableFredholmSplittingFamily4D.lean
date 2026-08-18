import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableKernelComplementTrivialization4D

/-!
# C1 Fredholm splitting families

A smooth determinant-line family needs regularity of both pieces of the actual
orthogonal splitting

`E = ker H_a ⊕ (ker H_a)ᗮ`.

This packet combines the fixed-label differentiable kernel basis with the
unitary differentiable trivialization of the genuine kernel complements.  Both
are expressed in the common ambient Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableFredholmSplittingFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D
open P0EFTJanusProgramPDifferentiableKernelComplementTrivialization4D
open P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode]

/-- Complete C1 orthogonal Fredholm splitting data for one self-adjoint family. -/
structure DifferentiableFredholmSplittingFamilyData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  selfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)
  kernels : DifferentiableFiniteKernelBasisFamilyData operator ZeroMode
  complementTrivialization :
    SelfAdjointKernelComplementFamilyTrivializationData operator selfAdjoint
  complementRegularity :
    DifferentiableKernelComplementTrivializationData complementTrivialization

namespace DifferentiableFredholmSplittingFamilyData

/-- Named kernel vectors are C1 in the ambient Hilbert space. -/
theorem kernelVector_differentiable
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode)
    (mode : ZeroMode) :
    Differentiable Real
      (fun parameter : Real => data.kernels.kernels.vector parameter mode) :=
  data.kernels.vector_differentiable mode

/-- Every fixed base-complement vector has a C1 transported ambient vector. -/
theorem complementVector_differentiable
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode)
    (vector : SelfAdjointKernelComplement (operator 0)) :
    Differentiable Real
      (fun parameter : Real =>
        ((data.complementTrivialization.transport parameter vector :
            SelfAdjointKernelComplement (operator parameter)) : E)) :=
  data.complementRegularity.transport_differentiable vector

/-- Named vectors remain genuine zero modes pointwise. -/
theorem kernelVector_zero
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode)
    (parameter : Real) (mode : ZeroMode) :
    operator parameter (data.kernels.kernels.vector parameter mode) = 0 :=
  data.kernels.kernels.vector_mem_kernel parameter mode

/-- Transported complement vectors remain in the true orthogonal complement of
the actual kernel. -/
theorem complementVector_mem
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode)
    (parameter : Real)
    (vector : SelfAdjointKernelComplement (operator 0)) :
    ((data.complementTrivialization.transport parameter vector :
        SelfAdjointKernelComplement (operator parameter)) : E) ∈
      (operator parameter).kerᗮ :=
  (data.complementTrivialization.transport parameter vector).property

/-- The complement frame remains unitary. -/
theorem complementVector_norm
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode)
    (parameter : Real)
    (vector : SelfAdjointKernelComplement (operator 0)) :
    ‖data.complementTrivialization.transport parameter vector‖ = ‖vector‖ :=
  data.complementTrivialization.transport_norm parameter vector

/-- The finite kernel rank remains the fixed number of named physical modes. -/
theorem kernel_finrank_eq_card
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.finrank Real (operator parameter).ker = Fintype.card ZeroMode :=
  data.kernels.kernels.kernel_finrank_eq_card parameter

/-- Public C1 Fredholm-splitting checkpoint. -/
theorem differentiable_fredholm_splitting_family_gate
    (operator : Real → E →L[Real] E)
    (data : DifferentiableFredholmSplittingFamilyData operator ZeroMode) :
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => data.kernels.kernels.vector parameter mode)) ∧
    (∀ vector : SelfAdjointKernelComplement (operator 0),
      Differentiable Real
        (fun parameter : Real =>
          ((data.complementTrivialization.transport parameter vector :
              SelfAdjointKernelComplement (operator parameter)) : E))) ∧
    (∀ parameter mode,
      operator parameter (data.kernels.kernels.vector parameter mode) = 0) ∧
    (∀ (parameter : Real)
        (vector : SelfAdjointKernelComplement (operator 0)),
      ((data.complementTrivialization.transport parameter vector :
          SelfAdjointKernelComplement (operator parameter)) : E) ∈
        (operator parameter).kerᗮ) ∧
    (∀ parameter,
      Module.finrank Real (operator parameter).ker = Fintype.card ZeroMode) :=
  ⟨data.kernelVector_differentiable,
    data.complementVector_differentiable,
    data.kernelVector_zero,
    data.complementVector_mem,
    data.kernel_finrank_eq_card⟩

end DifferentiableFredholmSplittingFamilyData

end
end P0EFTJanusProgramPDifferentiableFredholmSplittingFamily4D
end JanusFormal
