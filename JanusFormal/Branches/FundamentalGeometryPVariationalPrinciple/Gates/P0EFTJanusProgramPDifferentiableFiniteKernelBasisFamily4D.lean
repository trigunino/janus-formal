import Mathlib.Analysis.Calculus.FDeriv.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelBasisFamily4D

/-!
# Differentiable named bases of finite kernels

The algebraic family `FiniteKernelBasisFamilyData` keeps one fixed finite label
type but does not assert parameter regularity.  For determinant-line geometry
it is enough to formulate the first regularity layer in the fixed ambient
Hilbert space: each named kernel vector varies differentiably with the family
parameter.

This avoids attempting to differentiate a map whose codomain is the varying
subtype `ker H_a`.  All sector labels and coordinate transports remain those of
the existing algebraic family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteKernelBasisFamily4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [Fintype ZeroMode] [DecidableEq ZeroMode]

/-- C1 regularity of a fixed-label basis of the varying actual kernels,
expressed in the common ambient space. -/
structure DifferentiableFiniteKernelBasisFamilyData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  kernels : FiniteKernelBasisFamilyData operator ZeroMode
  vector_differentiable : ∀ mode,
    Differentiable Real (fun parameter : Real => kernels.vector parameter mode)

namespace DifferentiableFiniteKernelBasisFamilyData

/-- Every named kernel vector is continuous as an ambient family. -/
theorem vector_continuous
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFiniteKernelBasisFamilyData operator ZeroMode)
    (mode : ZeroMode) :
    Continuous (fun parameter : Real => data.kernels.vector parameter mode) :=
  (data.vector_differentiable mode).continuous

/-- Pointwise differentiability of every named ambient kernel vector. -/
theorem vector_differentiableAt
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) (mode : ZeroMode) :
    DifferentiableAt Real
      (fun current : Real => data.kernels.vector current mode) parameter :=
  (data.vector_differentiable mode) parameter

/-- Differentiable regularity does not alter the exact kernel equation. -/
theorem vector_mem_kernel
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) (mode : ZeroMode) :
    operator parameter (data.kernels.vector parameter mode) = 0 :=
  data.kernels.vector_mem_kernel parameter mode

/-- Differentiable regularity keeps the same coordinate-preserving transport. -/
theorem kernelTransport_basis
    {operator : Real → E →L[Real] E}
    (data : DifferentiableFiniteKernelBasisFamilyData operator ZeroMode)
    (first second : Real) (mode : ZeroMode) :
    data.kernels.kernelTransport first second (data.kernels.basis first mode) =
      data.kernels.basis second mode :=
  data.kernels.kernelTransport_basis first second mode

/-- Public C1 named-kernel-family checkpoint. -/
theorem differentiable_finite_kernel_basis_family_gate
    (operator : Real → E →L[Real] E)
    (data : DifferentiableFiniteKernelBasisFamilyData operator ZeroMode) :
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => data.kernels.vector parameter mode)) ∧
    (∀ mode,
      Continuous
        (fun parameter : Real => data.kernels.vector parameter mode)) ∧
    (∀ parameter mode,
      operator parameter (data.kernels.vector parameter mode) = 0) ∧
    (∀ first second mode,
      data.kernels.kernelTransport first second
          (data.kernels.basis first mode) =
        data.kernels.basis second mode) :=
  ⟨data.vector_differentiable,
    data.vector_continuous,
    data.vector_mem_kernel,
    data.kernelTransport_basis⟩

end DifferentiableFiniteKernelBasisFamilyData

end
end P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D
end JanusFormal
