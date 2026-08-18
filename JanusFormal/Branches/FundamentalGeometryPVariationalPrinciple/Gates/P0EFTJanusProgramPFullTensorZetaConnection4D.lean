import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorZetaConnection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Covariant derivative in the canonical finite Fredholm frame, valued in the
full tensor-product determinant fibre. -/
def fullTensorZetaConnectionAt
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) (value derivative : Complex) :
    fredholm.fullTensorDeterminantLine parameter :=
  fredholm.fullTensorDeterminantSection parameter
    (relativeZetaConnectionAt zetaFamily.toZetaFamily parameter value derivative)

end
end P0EFTJanusProgramPFullTensorZetaConnection4D
end JanusFormal
