import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeBasis4D

/-!
# Finite kernel families with one fixed named basis type

A family of Fredholm Hessians may have nontrivial kernels even when its reduced
operators are uniformly invertible.  To construct a determinant line one must
track those zero modes along the family.

This file fixes one finite label type `ZeroMode` and a basis

`e_i(a) : basis of ker H_a`

at every parameter.  The common labels canonically transport zero modes between
any two parameters by keeping their coordinates fixed.  Kernel dimension and
any fixed sector multiplicities are consequently constant throughout the
family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelBasisFamily4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteKernelNamedModeBasis4D
open P0EFTJanusProgramPFiniteKernelNamedModes4D

variable {E ZeroMode Sector : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [Fintype ZeroMode] [DecidableEq ZeroMode]
  [Fintype Sector] [DecidableEq Sector]

/-- A basis of every actual kernel, indexed by one fixed finite physical type. -/
structure FiniteKernelBasisFamilyData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  basis : ∀ parameter, Basis ZeroMode Real (operator parameter).ker

namespace FiniteKernelBasisFamilyData

/-- Ambient named zero-mode vector. -/
def vector
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) (mode : ZeroMode) : E :=
  (data.basis parameter mode).1

/-- Every named vector is annihilated by the current operator. -/
theorem vector_mem_kernel
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) (mode : ZeroMode) :
    operator parameter (data.vector parameter mode) = 0 :=
  (data.basis parameter mode).2

/-- Existing named-mode model at each parameter. -/
def namedFamily
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) :
    FiniteKernelNamedModeFamily (operator parameter) ZeroMode :=
  finiteKernelNamedModeFamilyOfBasis (data.basis parameter)

@[simp]
theorem namedFamily_vector
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) (mode : ZeroMode) :
    (data.namedFamily parameter).vector mode = data.vector parameter mode :=
  rfl

/-- Coordinates of a zero mode at one parameter. -/
def analyze
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) :
    (operator parameter).ker →ₗ[Real] (ZeroMode → Real) :=
  (data.basis parameter).equivFun.toLinearMap

/-- Synthesis in the kernel at one parameter. -/
def synthesize
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) :
    (ZeroMode → Real) →ₗ[Real] (operator parameter).ker :=
  (data.basis parameter).equivFun.symm.toLinearMap

/-- Canonical zero-mode transport: keep the fixed physical coordinates. -/
def kernelTransport
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (first second : Real) :
    (operator first).ker ≃ₗ[Real] (operator second).ker :=
  (data.basis first).equivFun.trans (data.basis second).equivFun.symm

/-- Transport sends each named basis vector to the identically named vector. -/
@[simp]
theorem kernelTransport_basis
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (first second : Real) (mode : ZeroMode) :
    data.kernelTransport first second (data.basis first mode) =
      data.basis second mode := by
  apply (data.basis second).equivFun.injective
  simp [kernelTransport]

/-- Identity transport. -/
@[simp]
theorem kernelTransport_self
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) :
    data.kernelTransport parameter parameter = LinearEquiv.refl Real _ := by
  ext zeroMode
  apply (data.basis parameter).equivFun.injective
  simp [kernelTransport]

/-- Exact composition law of kernel transports. -/
theorem kernelTransport_trans
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.kernelTransport second third).comp
        (data.kernelTransport first second) =
      data.kernelTransport first third := by
  ext zeroMode
  apply (data.basis third).equivFun.injective
  simp [kernelTransport]

/-- Kernel dimension is constant and equal to the number of physical labels. -/
theorem kernel_finrank_eq_card
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.finrank Real (operator parameter).ker = Fintype.card ZeroMode :=
  finiteKernelNamedModeFamilyOfBasis_finrank (data.basis parameter)

/-- Exact reconstruction after transport. -/
theorem transport_synthesize
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelBasisFamilyData operator ZeroMode)
    (first second : Real) (coefficient : ZeroMode → Real) :
    data.kernelTransport first second
        ((data.basis first).equivFun.symm coefficient) =
      (data.basis second).equivFun.symm coefficient := by
  apply (data.basis second).equivFun.injective
  simp [kernelTransport]

/-- Public finite-kernel-family checkpoint. -/
theorem finite_kernel_basis_family_gate
    (operator : Real → E →L[Real] E)
    (data : FiniteKernelBasisFamilyData operator ZeroMode) :
    (∀ parameter mode,
      operator parameter (data.vector parameter mode) = 0) ∧
      (∀ first second mode,
        data.kernelTransport first second (data.basis first mode) =
          data.basis second mode) ∧
      (∀ first second third,
        (data.kernelTransport second third).comp
            (data.kernelTransport first second) =
          data.kernelTransport first third) ∧
      (∀ parameter,
        Module.finrank Real (operator parameter).ker =
          Fintype.card ZeroMode) :=
  ⟨data.vector_mem_kernel,
    data.kernelTransport_basis,
    data.kernelTransport_trans,
    data.kernel_finrank_eq_card⟩

end FiniteKernelBasisFamilyData

/-- Fixed physical sector assignment for the named kernel basis family. -/
structure FiniteKernelSectorBasisFamilyData
    (operator : Real → E →L[Real] E)
    (ZeroMode Sector : Type*)
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    [Fintype Sector] [DecidableEq Sector] where
  kernels : FiniteKernelBasisFamilyData operator ZeroMode
  sectorOf : ZeroMode → Sector

namespace FiniteKernelSectorBasisFamilyData

/-- Multiplicity of one physical sector, independent of the parameter. -/
def multiplicity
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelSectorBasisFamilyData operator ZeroMode Sector)
    (sector : Sector) : Nat :=
  Fintype.card {mode : ZeroMode // data.sectorOf mode = sector}

/-- Sector multiplicities partition the fixed zero-mode type. -/
theorem sum_multiplicity
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelSectorBasisFamilyData operator ZeroMode Sector) :
    ∑ sector : Sector, data.multiplicity sector = Fintype.card ZeroMode := by
  simpa [multiplicity] using Fintype.sum_card_fiberwise data.sectorOf

/-- Kernel dimension is the same sum of sector multiplicities for every
parameter. -/
theorem kernel_finrank_eq_sum_multiplicity
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelSectorBasisFamilyData operator ZeroMode Sector)
    (parameter : Real) :
    Module.finrank Real (operator parameter).ker =
      ∑ sector : Sector, data.multiplicity sector := by
  rw [data.kernels.kernel_finrank_eq_card parameter]
  exact data.sum_multiplicity.symm

/-- Transport preserves sector labels because it preserves the named basis
index itself. -/
theorem transport_preserves_named_sector
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelSectorBasisFamilyData operator ZeroMode Sector)
    (first second : Real) (mode : ZeroMode) :
    data.kernels.kernelTransport first second
        (data.kernels.basis first mode) =
      data.kernels.basis second mode ∧
    data.sectorOf mode = data.sectorOf mode :=
  ⟨data.kernels.kernelTransport_basis first second mode, rfl⟩

/-- Public sector-classified kernel-family checkpoint. -/
theorem finite_kernel_sector_basis_family_gate
    (operator : Real → E →L[Real] E)
    (data : FiniteKernelSectorBasisFamilyData operator ZeroMode Sector) :
    (∀ parameter,
      Module.finrank Real (operator parameter).ker =
        ∑ sector : Sector, data.multiplicity sector) ∧
      (∀ first second mode,
        data.kernels.kernelTransport first second
            (data.kernels.basis first mode) =
          data.kernels.basis second mode) :=
  ⟨data.kernel_finrank_eq_sum_multiplicity,
    data.kernels.kernelTransport_basis⟩

end FiniteKernelSectorBasisFamilyData

end
end P0EFTJanusProgramPFiniteKernelBasisFamily4D
end JanusFormal
