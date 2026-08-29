import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaConnection4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorZetaParallel4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPFullTensorZetaConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

theorem fullTensorZetaSection_parallel
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    fullTensorZetaConnectionAt fredholm zetaFamily parameter
        (relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          zetaFamily.toZetaFamily parameter) = 0 := by
  unfold fullTensorZetaConnectionAt
  rw [relativeZetaDeterminantCoordinate_parallel]
  simp [SelfAdjointFredholmDeterminantFamilyData.fullTensorDeterminantSection]

end
end P0EFTJanusProgramPFullTensorZetaParallel4D
end JanusFormal
