import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorCollapseFormula4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

@[simp] theorem fullTensorCollapse_formula
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (z : Complex) :
    data.fullTensorDeterminantCollapse parameter
        (data.fullTensorDeterminantSection parameter z) =
      z • data.complexifiedDeterminantFrame parameter := by
  simp [fullTensorDeterminantCollapse, fullTensorDeterminantSection]

end SelfAdjointFredholmDeterminantFamilyData
end
end P0EFTJanusProgramPFullTensorCollapseFormula4D
end JanusFormal
