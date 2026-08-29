import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

/-!
# Functorial laws of the actual Fredholm determinant transport

The existing kernel/cokernel transports induce identity and composition laws
on the actual Fredholm determinant fibres. No second transport family is
introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportLaws4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

noncomputable section

open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

@[simp]
theorem cokernelTransport_self
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.cokernelTransport parameter parameter = LinearEquiv.refl Real _ := by
  ext value
  apply (data.cokernelKernelEquiv parameter).injective
  rw [data.cokernelKernelEquiv_transport]
  simp

@[simp]
theorem kernelTopTransport_self
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.kernelTopTransport parameter parameter = LinearEquiv.refl Real _ := by
  apply LinearEquiv.ext
  intro value
  change finiteKernelDeterminantTransport data.kernels parameter parameter value = value
  rw [data.kernels.finiteKernelDeterminantTransport_self]
  rfl

@[simp]
theorem cokernelTopTransport_self
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.cokernelTopTransport parameter parameter = LinearEquiv.refl Real _ := by
  apply LinearEquiv.ext
  intro value
  change
    exteriorPower.map determinantDegree
        (data.cokernelTransport parameter parameter).toLinearMap value = value
  rw [data.cokernelTransport_self]
  simp

/-- Exact composition of top-kernel transports. -/
theorem kernelTopTransport_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.kernelTopTransport first second).trans
        (data.kernelTopTransport second third) =
      data.kernelTopTransport first third := by
  apply LinearEquiv.ext
  intro value
  change
    finiteKernelDeterminantTransport data.kernels second third
        (finiteKernelDeterminantTransport data.kernels first second value) =
      finiteKernelDeterminantTransport data.kernels first third value
  have h := data.kernels.finiteKernelDeterminantTransport_trans
    first second third
  exact LinearMap.congr_fun h value

/-- Exact composition of top-cokernel transports. -/
theorem cokernelTopTransport_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.cokernelTopTransport first second).trans
        (data.cokernelTopTransport second third) =
      data.cokernelTopTransport first third := by
  apply LinearEquiv.ext
  intro value
  change
    exteriorPower.map determinantDegree
        (data.cokernelTransport second third).toLinearMap
      (exteriorPower.map determinantDegree
        (data.cokernelTransport first second).toLinearMap value) =
      exteriorPower.map determinantDegree
        (data.cokernelTransport first third).toLinearMap value
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have h := data.cokernelTransport_trans first second third
  have hLinear := congrArg LinearEquiv.toLinearMap h
  rw [hLinear]

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportLaws4D
end JanusFormal
