import Mathlib.LinearAlgebra.TensorProduct.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

namespace JanusFormal

namespace P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
end P0EFTJanusProgramPSelfAdjointFredholmComplexification4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open scoped TensorProduct

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

abbrev complexifiedDeterminantLine
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :=
  Complex ⊗[Real] (data.determinantLine parameter)

def complexifiedDeterminantFrame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) : data.complexifiedDeterminantLine parameter :=
  TensorProduct.tmul Real (1 : Complex) (data.determinantFrame parameter)

def complexifiedDeterminantSection
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Complex) :
    data.complexifiedDeterminantLine parameter :=
  coordinate • data.complexifiedDeterminantFrame parameter

theorem complexifiedDeterminantSection_one
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.complexifiedDeterminantSection parameter 1 =
      data.complexifiedDeterminantFrame parameter := by
  simp [complexifiedDeterminantSection]

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
