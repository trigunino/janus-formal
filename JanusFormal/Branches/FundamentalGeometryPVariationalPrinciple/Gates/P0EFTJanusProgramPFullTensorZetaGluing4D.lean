import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaAtlas4D

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorZetaGluing4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPFullTensorCollapseFormula4D
open P0EFTJanusProgramPFullTensorZetaAtlas4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

variable {E Index : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

theorem localFullTensorSection_transition
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter •
        localFullTensorSection fredholm atlas first parameter =
      localFullTensorSection fredholm atlas second parameter := by
  unfold localFullTensorSection
  apply (fredholm.fullTensorDeterminantCollapse parameter).injective
  simp only [map_smul, fredholm.fullTensorCollapse_formula, smul_smul]
  rw [relativeZetaLocalDeterminant_transition atlas first second parameter]

end
end P0EFTJanusProgramPFullTensorZetaGluing4D
end JanusFormal
