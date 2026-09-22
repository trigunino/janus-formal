import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CoupledBRSTOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedPerturbationCore4D

/-! Operator cores for both BRST sectors, retaining the full physical coupling. -/
namespace JanusFormal.P0EFTJanusProgramPT12CoupledBRSTCore4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductClosure4D
open P0EFTJanusProgramPT12ProductCore4D
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
open P0EFTJanusProgramPT12BoundedPerturbationCore4D
open P0EFTJanusProgramPT12CoupledBRSTOperator4D
variable {D V H : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D] [CompleteSpace D]
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

theorem coupledBRSTOperator_isClosed (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (hA : (A.toPMap ⊤).IsClosed) (hF : F.IsClosed) :
    (coupledBRSTOperator A F U W R).IsClosed :=
  boundedPerturbation_isClosed _ _ (productOperator_isClosed _ _ hA hF)

theorem coupledBRSTOperator_hasCore (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (hA : (A.toPMap ⊤).IsClosed) (hF : F.IsClosed)
    (S : Submodule Real D) (T : Submodule Real V)
    (hS : (A.toPMap ⊤).HasCore S) (hT : F.HasCore T) :
    (coupledBRSTOperator A F U W R).HasCore (productCore S T) :=
  boundedPerturbation_hasCore _ _ (productOperator_isClosed _ _ hA hF).isClosable _
    (productOperator_hasCore _ _ hA hF S T hS hT)

/-- Only the unbounded BRST factor changes when closing the smooth restriction. -/
theorem coupledBRSTOperator_restriction_closure (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (hA : (A.toPMap ⊤).IsClosed) (hF : F.IsClosable)
    (S : Submodule Real D) (T : Submodule Real V) (hS : (A.toPMap ⊤).HasCore S) :
    ((coupledBRSTOperator A F U W R).domRestrict (productCore S T)).closure =
      coupledBRSTOperator A (F.domRestrict T).closure U W R := by
  have hAR := hA.isClosable.leIsClosable
    (show (A.toPMap ⊤).domRestrict S ≤ A.toPMap ⊤ from LinearPMap.domRestrict_le)
  have hFR := hF.leIsClosable (show F.domRestrict T ≤ F from LinearPMap.domRestrict_le)
  unfold coupledBRSTOperator
  rw [boundedPerturbation_restriction, productOperator_restriction,
    boundedPerturbation_closure _ _ (productOperator_isClosable _ _ hAR hFR),
    productOperator_closure _ _ hAR hFR, hS.closure_eq]

end
end JanusFormal.P0EFTJanusProgramPT12CoupledBRSTCore4D
