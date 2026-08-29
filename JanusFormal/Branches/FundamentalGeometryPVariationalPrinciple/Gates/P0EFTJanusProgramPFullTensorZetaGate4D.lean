import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPZetaTensorIdentification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaParallel4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorZetaGate4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPZetaTensorIdentification4D
open P0EFTJanusProgramPFullTensorZetaConnection4D
open P0EFTJanusProgramPFullTensorZetaParallel4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Terminal generic full tensor determinant checkpoint. -/
theorem full_tensor_zeta_gate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    (∀ parameter,
      fredholm.fullTensorDeterminantCollapse parameter
          (selfAdjointFredholmZetaFullTensorSection fredholm zetaFamily parameter) =
        selfAdjointFredholmZetaDeterminantSection fredholm zetaFamily parameter) ∧
    (∀ parameter,
      relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter ≠ 0) ∧
    (∀ parameter,
      fullTensorZetaConnectionAt fredholm zetaFamily parameter
          (relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter)
          (relativeZetaDeterminantCoordinateDerivative
            zetaFamily.toZetaFamily parameter) = 0) :=
  ⟨zetaFullTensor_collapse fredholm zetaFamily,
    fun parameter => relativeZetaDeterminantCoordinate_ne_zero
      zetaFamily.toZetaFamily parameter,
    fullTensorZetaSection_parallel fredholm zetaFamily⟩

end
end P0EFTJanusProgramPFullTensorZetaGate4D
end JanusFormal
