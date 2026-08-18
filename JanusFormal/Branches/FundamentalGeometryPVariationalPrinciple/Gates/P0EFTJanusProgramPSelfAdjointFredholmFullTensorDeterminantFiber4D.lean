import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminant4D

namespace JanusFormal

namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminant4D
open scoped TensorProduct

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

abbrev fullTensorDeterminantLine
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :=
  data.complexifiedDeterminantLine parameter ⊗[Complex]
    reducedInvertibleDeterminantLine

def fullTensorDeterminantSection
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (reducedCoordinate : Complex) :
    data.fullTensorDeterminantLine parameter :=
  TensorProduct.tmul Complex
    (data.complexifiedDeterminantFrame parameter) reducedCoordinate

/-- Scalar multiplication of a full determinant section is exactly
multiplication of its reduced complex coordinate.  Downstream atlas and gauge
proofs use this API instead of depending directly on tensor-product rewrite
lemmas. -/
@[simp]
theorem fullTensorDeterminantSection_smul
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (scalar coordinate : Complex) :
    scalar • data.fullTensorDeterminantSection parameter coordinate =
      data.fullTensorDeterminantSection parameter (scalar * coordinate) := by
  change scalar • TensorProduct.tmul Complex
      (data.complexifiedDeterminantFrame parameter) coordinate =
    TensorProduct.tmul Complex
      (data.complexifiedDeterminantFrame parameter) (scalar • coordinate)
  rw [TensorProduct.tmul_smul]

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
