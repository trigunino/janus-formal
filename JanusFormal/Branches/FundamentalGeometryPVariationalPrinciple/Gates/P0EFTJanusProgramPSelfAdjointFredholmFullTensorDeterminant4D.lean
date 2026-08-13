import Mathlib.LinearAlgebra.TensorProduct.Associator
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexification4D

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminant4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- The invertible reduced determinant line is canonically the scalar line. -/
abbrev reducedInvertibleDeterminantLine := Complex

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminant4D
end JanusFormal
