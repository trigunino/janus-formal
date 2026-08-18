import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorAtlasConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorCollapseFormula4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorGauge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPFullTensorCollapseFormula4D
open P0EFTJanusProgramPFullTensorAtlasConnection4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

variable {E Index : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Exact gauge covariance of the connection valued in the full tensor line. -/
theorem localFullTensorConnection_gauge
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real)
    (value derivative : Complex) :
    localFullTensorConnectionAt fredholm atlas second parameter
        (relativeZetaTransition atlas first second parameter * value)
        (relativeZetaTransitionDerivative atlas first second parameter * value +
          relativeZetaTransition atlas first second parameter * derivative) =
      relativeZetaTransition atlas first second parameter •
        localFullTensorConnectionAt fredholm atlas first parameter value derivative := by
  unfold localFullTensorConnectionAt
  apply (fredholm.fullTensorDeterminantCollapse parameter).injective
  rw [fredholm.fullTensorCollapse_formula, map_smul,
    fredholm.fullTensorCollapse_formula]
  have h := relativeZetaLocalConnection_gauge_covariant
    atlas first second parameter value derivative
  simpa [smul_smul] using congrArg
    (fun coordinate : Complex =>
      coordinate • fredholm.complexifiedDeterminantFrame parameter) h

end
end P0EFTJanusProgramPFullTensorGauge4D
end JanusFormal
