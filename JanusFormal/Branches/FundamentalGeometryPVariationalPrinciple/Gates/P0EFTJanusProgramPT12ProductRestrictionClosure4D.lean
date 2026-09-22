import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductCore4D

namespace JanusFormal.P0EFTJanusProgramPT12ProductRestrictionClosure4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductClosure4D
open P0EFTJanusProgramPT12ProductCore4D
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace Real H]
variable [NormedAddCommGroup K] [InnerProductSpace Real K]

theorem productOperator_restriction_closure_eq
    (A A₀ : H →ₗ.[Real] H) (B B₀ : K →ₗ.[Real] K)
    (hA : A.IsClosed) (hB : B.IsClosed) (S : Submodule Real H) (T : Submodule Real K)
    (hS : (A.domRestrict S).closure = A₀) (hT : (B.domRestrict T).closure = B₀) :
    ((productOperator A B).domRestrict (productCore S T)).closure = productOperator A₀ B₀ := by
  rw [productOperator_restriction, productOperator_closure _ _
    (hA.isClosable.leIsClosable (show A.domRestrict S ≤ A from LinearPMap.domRestrict_le))
    (hB.isClosable.leIsClosable (show B.domRestrict T ≤ B from LinearPMap.domRestrict_le)), hS, hT]

end
end JanusFormal.P0EFTJanusProgramPT12ProductRestrictionClosure4D
