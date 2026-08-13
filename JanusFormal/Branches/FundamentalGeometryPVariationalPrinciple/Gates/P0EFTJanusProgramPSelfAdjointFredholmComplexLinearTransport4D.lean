import Mathlib.LinearAlgebra.TensorProduct.Tower
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFramePreservation4D

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmComplexLinearTransport4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmFramePreservation4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Genuine complex-linear extension of the actual Fredholm transport. -/
def complexLinearDeterminantTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.complexifiedDeterminantLine first ≃ₗ[Complex]
      data.complexifiedDeterminantLine second :=
  TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Complex Complex)
    (data.determinantTransport first second)

/-- On pure tensors only the actual Fredholm factor is transported. -/
@[simp]
theorem complexLinearDeterminantTransport_tmul
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) (coordinate : Complex)
    (value : data.determinantLine first) :
    data.complexLinearDeterminantTransport first second
        (TensorProduct.tmul Real coordinate value) =
      TensorProduct.tmul Real coordinate
        (data.determinantTransport first second value) := by
  simp [complexLinearDeterminantTransport]

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmComplexLinearTransport4D
end JanusFormal
