import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorCollapseFormula4D

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Full tensor-product determinant section carrying the intrinsic zeta vector. -/
def selfAdjointFredholmZetaFullTensorSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) : fredholm.fullTensorDeterminantLine parameter :=
  fredholm.fullTensorDeterminantSection parameter
    (relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter)

end
end P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
end JanusFormal
