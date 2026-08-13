import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorCollapseFormula4D

namespace JanusFormal
namespace P0EFTJanusProgramPZetaTensorIdentification4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPFullTensorCollapseFormula4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

theorem zetaFullTensor_collapse
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    fredholm.fullTensorDeterminantCollapse parameter
        (selfAdjointFredholmZetaFullTensorSection fredholm zetaFamily parameter) =
      selfAdjointFredholmZetaDeterminantSection fredholm zetaFamily parameter := by
  rw [fullTensorCollapse_formula]
  exact (selfAdjointFredholmZetaDeterminantSection_eq
    fredholm zetaFamily parameter).symm

end
end P0EFTJanusProgramPZetaTensorIdentification4D
end JanusFormal
