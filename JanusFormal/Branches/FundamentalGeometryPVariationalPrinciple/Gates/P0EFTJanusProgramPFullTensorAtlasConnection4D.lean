import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaAtlas4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorAtlasConnection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

variable {E Index : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Local zeta connection lifted to the genuine full tensor determinant fibre. -/
def localFullTensorConnectionAt
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) (value derivative : Complex) :
    fredholm.fullTensorDeterminantLine parameter :=
  fredholm.fullTensorDeterminantSection parameter
    (relativeZetaLocalConnectionAt atlas index parameter value derivative)

end
end P0EFTJanusProgramPFullTensorAtlasConnection4D
end JanusFormal
