import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D

/-!
# Actual determinant lines for self-adjoint Fredholm families

For a bounded self-adjoint operator with a finite kernel and a positive gap on
its true kernel complement, the range is exactly `(ker H)ᗮ`.  Hence

`E / range H ≃ ker H`.

This file uses that canonical equivalence to construct the actual real
Fredholm determinant fibre

`Hom(det coker H, det ker H)`

at every parameter of a family.  A fixed named basis of the kernels transports
both kernels and cokernels between parameters and therefore induces genuine
linear equivalences of determinant fibres.

This is the finite-dimensional Fredholm line.  The reduced zeta determinant is
still a separate nonzero scalar coordinate on the invertible complement; its
complex tensor-product coupling to this real line is not hidden here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- One self-adjoint Fredholm family together with a fixed named basis of every
actual kernel. -/
structure SelfAdjointFredholmDeterminantFamilyData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    [LinearOrder ZeroMode] where
  selfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)
  gap : ∀ parameter,
    SelfAdjointKernelComplementGapData
      (operator parameter) (selfAdjoint parameter)
  kernels : FiniteKernelBasisFamilyData operator ZeroMode

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Algebraic cokernel of one family member. -/
abbrev cokernel
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :=
  E ⧸ (operator parameter).range

/-- The self-adjoint gap identifies the range with the orthogonal complement
of the actual kernel. -/
theorem range_eq_kernel_orthogonal
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    (operator parameter).range = (operator parameter).kerᗮ :=
  selfAdjoint_operator_range_eq_kernelComplement
    (operator parameter) (data.selfAdjoint parameter) (data.gap parameter)

/-- The actual range and actual kernel are complementary. -/
theorem rangeKernel_isCompl
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    IsCompl (operator parameter).range (operator parameter).ker := by
  rw [data.range_eq_kernel_orthogonal parameter]
  exact (operator parameter).ker.isCompl_orthogonal.symm

/-- Canonical self-adjoint identification `coker H ≃ ker H`. -/
def cokernelKernelEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.cokernel parameter ≃ₗ[Real] (operator parameter).ker :=
  (operator parameter).range.quotientEquivOfIsCompl
    (operator parameter).ker (data.rangeKernel_isCompl parameter)

/-- The cokernel dimension is the number of fixed physical zero-mode labels. -/
theorem cokernel_finrank_eq_card
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.finrank Real (data.cokernel parameter) = Fintype.card ZeroMode := by
  calc
    Module.finrank Real (data.cokernel parameter) =
        Module.finrank Real (operator parameter).ker :=
      (data.cokernelKernelEquiv parameter).finrank_eq
    _ = Fintype.card ZeroMode :=
      data.kernels.kernel_finrank_eq_card parameter

/-- Common determinant degree. -/
abbrev determinantDegree : Nat := Fintype.card ZeroMode

/-- Top exterior power of the actual cokernel. -/
abbrev cokernelTop
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :=
  ⋀[Real]^(determinantDegree (ZeroMode := ZeroMode)) (data.cokernel parameter)

/-- Top exterior power of the actual kernel. -/
abbrev kernelTop
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :=
  FiniteKernelDeterminantFiber data.kernels parameter

/-- Actual Fredholm determinant fibre `Hom(det coker H, det ker H)`. -/
abbrev determinantLine
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :=
  data.cokernelTop parameter →ₗ[Real] data.kernelTop parameter

/-- Canonical nonzero frame induced by `coker H ≃ ker H`. -/
def determinantFrame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) : data.determinantLine parameter :=
  exteriorPower.map (determinantDegree (ZeroMode := ZeroMode))
    (data.cokernelKernelEquiv parameter).toLinearMap

/-- Exterior-power equivalence induced by a linear equivalence. -/
def exteriorPowerEquiv
    {first second : Type*}
    [AddCommGroup first] [Module Real first]
    [AddCommGroup second] [Module Real second]
    (degree : Nat) (equivalence : first ≃ₗ[Real] second) :
    ⋀[Real]^degree first ≃ₗ[Real] ⋀[Real]^degree second :=
  LinearEquiv.ofBijective
    (exteriorPower.map degree equivalence.toLinearMap)
    ⟨exteriorPower.map_injective_field equivalence.injective,
      exteriorPower.map_surjective equivalence.surjective⟩

/-- Canonical cokernel transport obtained by passing through the named kernels. -/
def cokernelTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.cokernel first ≃ₗ[Real] data.cokernel second :=
  (data.cokernelKernelEquiv first).trans
    ((data.kernels.kernelTransport first second).trans
      (data.cokernelKernelEquiv second).symm)

/-- Kernel top-exterior transport. -/
def kernelTopTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.kernelTop first ≃ₗ[Real] data.kernelTop second :=
  exteriorPowerEquiv (determinantDegree (ZeroMode := ZeroMode))
    (data.kernels.kernelTransport first second)

/-- Cokernel top-exterior transport. -/
def cokernelTopTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.cokernelTop first ≃ₗ[Real] data.cokernelTop second :=
  exteriorPowerEquiv (determinantDegree (ZeroMode := ZeroMode))
    (data.cokernelTransport first second)

/-- Genuine transport between the actual Fredholm determinant fibres. -/
def determinantTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.determinantLine first ≃ₗ[Real] data.determinantLine second :=
  (data.cokernelTopTransport first second).arrowCongr
    (data.kernelTopTransport first second)

/-- Cokernel transport preserves the kernel coordinate selected by
self-adjointness. -/
theorem cokernelKernelEquiv_transport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real)
    (value : data.cokernel first) :
    data.cokernelKernelEquiv second (data.cokernelTransport first second value) =
      data.kernels.kernelTransport first second
        (data.cokernelKernelEquiv first value) := by
  simp [cokernelTransport]

/-- Exact composition law of cokernel transports. -/
theorem cokernelTransport_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.cokernelTransport first second).trans
        (data.cokernelTransport second third) =
      data.cokernelTransport first third := by
  apply LinearEquiv.ext
  intro value
  apply (data.cokernelKernelEquiv third).injective
  simp only [LinearEquiv.trans_apply,
    data.cokernelKernelEquiv_transport]
  have hTransport := congrArg
    (fun transport => transport (data.cokernelKernelEquiv first value))
    (data.kernels.kernelTransport_trans first second third)
  simpa only [LinearEquiv.trans_apply] using hTransport

/-- The kernel top exterior fibre is one-dimensional. -/
theorem kernelTop_finrank_one
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.finrank Real (data.kernelTop parameter) = 1 :=
  finiteKernelDeterminantFiber_finrank_one data.kernels parameter

/-- The cokernel top exterior fibre is one-dimensional. -/
theorem cokernelTop_finrank_one
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.finrank Real (data.cokernelTop parameter) = 1 := by
  letI : FiniteDimensional Real (operator parameter).ker :=
    (data.gap parameter).kernel_finite
  letI : FiniteDimensional Real (data.cokernel parameter) :=
    FiniteDimensional.of_injective
      (data.cokernelKernelEquiv parameter).toLinearMap
      (data.cokernelKernelEquiv parameter).injective
  change Module.finrank Real
      (⋀[Real]^(Fintype.card ZeroMode) (data.cokernel parameter)) = 1
  rw [exteriorPower.finrank_eq, data.cokernel_finrank_eq_card parameter,
    Nat.choose_self]

/-- Every actual determinant fibre is one-dimensional. -/
theorem determinantLine_finrank_one
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.finrank Real (data.determinantLine parameter) = 1 := by
  letI : FiniteDimensional Real (operator parameter).ker :=
    (data.gap parameter).kernel_finite
  letI : FiniteDimensional Real (data.cokernel parameter) :=
    FiniteDimensional.of_injective
      (data.cokernelKernelEquiv parameter).toLinearMap
      (data.cokernelKernelEquiv parameter).injective
  change Module.finrank Real
      (data.cokernelTop parameter →ₗ[Real] data.kernelTop parameter) = 1
  rw [Module.finrank_linearMap, data.cokernelTop_finrank_one parameter,
    data.kernelTop_finrank_one parameter, Nat.one_mul]

/-- The canonical determinant frame is injective. -/
theorem determinantFrame_injective
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    Function.Injective (data.determinantFrame parameter) :=
  exteriorPower.map_injective_field
    (n := determinantDegree (ZeroMode := ZeroMode))
    (data.cokernelKernelEquiv parameter).injective

/-- The canonical determinant frame never vanishes. -/
theorem determinantFrame_ne_zero
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.determinantFrame parameter ≠ 0 := by
  letI : FiniteDimensional Real (operator parameter).ker :=
    (data.gap parameter).kernel_finite
  letI : FiniteDimensional Real (data.cokernel parameter) :=
    FiniteDimensional.of_injective
      (data.cokernelKernelEquiv parameter).toLinearMap
      (data.cokernelKernelEquiv parameter).injective
  letI : Nontrivial (data.cokernelTop parameter) :=
    Module.nontrivial_of_finrank_eq_succ (R := Real)
      (data.cokernelTop_finrank_one parameter)
  exact LinearMap.ne_zero_of_injective
    (data.determinantFrame_injective parameter)

/-- Determinant-fibre transport is bijective by construction. -/
theorem determinantTransport_bijective
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    Function.Bijective (data.determinantTransport first second) :=
  (data.determinantTransport first second).bijective

/-- Public actual self-adjoint Fredholm determinant-line checkpoint. -/
theorem self_adjoint_fredholm_determinant_line_family_gate
    (operator : Real → E →L[Real] E)
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter,
      (operator parameter).range = (operator parameter).kerᗮ) ∧
      (∀ parameter,
        Module.finrank Real (data.determinantLine parameter) = 1) ∧
      (∀ parameter, data.determinantFrame parameter ≠ 0) ∧
      (∀ first second,
        Function.Bijective (data.determinantTransport first second)) ∧
      (∀ first second third,
        (data.cokernelTransport first second).trans
            (data.cokernelTransport second third) =
          data.cokernelTransport first third) :=
  ⟨data.range_eq_kernel_orthogonal,
    data.determinantLine_finrank_one,
    data.determinantFrame_ne_zero,
    data.determinantTransport_bijective,
    data.cokernelTransport_trans⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
