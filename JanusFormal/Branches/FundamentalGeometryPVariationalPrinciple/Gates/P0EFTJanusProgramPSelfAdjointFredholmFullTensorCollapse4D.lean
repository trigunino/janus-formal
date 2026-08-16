import Mathlib.LinearAlgebra.TensorProduct.Associator
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
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
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
end JanusFormal
