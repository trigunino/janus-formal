import Mathlib.LinearAlgebra.TensorProduct.Associator
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D

namespace JanusFormal

namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

def fullTensorDeterminantCollapse
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.fullTensorDeterminantLine parameter ≃ₗ[Complex]
      data.complexifiedDeterminantLine parameter :=
  TensorProduct.rid Complex (data.complexifiedDeterminantLine parameter)

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
