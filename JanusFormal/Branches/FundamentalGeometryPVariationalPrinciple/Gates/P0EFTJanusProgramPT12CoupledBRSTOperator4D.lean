import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D

/-! Two BRST sectors coupled through all physical Hessian blocks. -/
namespace JanusFormal.P0EFTJanusProgramPT12CoupledBRSTOperator4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
variable {D V H : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D] [CompleteSpace D]
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

def coupledPhysicalLift (U : D →L[Real] H) (W : V →L[Real] H) : WithLp 2 (D × V) →L[Real] H :=
  U.comp (WithLp.fstL 2 Real D V) + W.comp (WithLp.sndL 2 Real D V)

def coupledPhysicalBlock (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H) :
    WithLp 2 (D × V) →L[Real] WithLp 2 (D × V) :=
  (coupledPhysicalLift U W).adjoint.comp (R.comp (coupledPhysicalLift U W))

theorem coupledPhysicalBlock_pairing (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (x y : WithLp 2 (D × V)) :
    inner Real (coupledPhysicalBlock U W R x) y =
      inner Real (R (U x.fst + W x.snd)) (U y.fst + W y.snd) :=
  (coupledPhysicalLift U W).adjoint_inner_left y _

theorem coupledPhysicalBlock_selfAdjoint (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (hR : IsSelfAdjoint R) : IsSelfAdjoint (coupledPhysicalBlock U W R) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  change inner Real (coupledPhysicalBlock U W R x) y = inner Real x (coupledPhysicalBlock U W R y)
  rw [← real_inner_comm x (coupledPhysicalBlock U W R y), coupledPhysicalBlock_pairing,
    coupledPhysicalBlock_pairing]
  exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR) _ _).trans (real_inner_comm _ _)

def coupledBRSTOperator (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H) :
    WithLp 2 (D × V) →ₗ.[Real] WithLp 2 (D × V) :=
  boundedPerturbation (productOperator (A.toPMap ⊤) F) (coupledPhysicalBlock U W R)

theorem coupledBRSTOperator_domain_iff (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H) (x : WithLp 2 (D × V)) :
    x ∈ (coupledBRSTOperator A F U W R).domain ↔ x.snd ∈ F.domain := by
  rw [coupledBRSTOperator, boundedPerturbation_domain, productOperator_domain_iff]
  simp

theorem coupledBRSTOperator_selfAdjoint (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (hA : IsSelfAdjoint A) (hF : IsSelfAdjoint F) (hR : IsSelfAdjoint R) :
    IsSelfAdjoint (coupledBRSTOperator A F U W R) :=
  boundedPerturbation_selfAdjoint _ _
    (productOperator_selfAdjoint _ _ (bounded_toPMap_selfAdjoint A
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA)) hF)
    (coupledPhysicalBlock_selfAdjoint U W R hR)

theorem coupledBRSTOperator_pairing (A : D →L[Real] D) (F : V →ₗ.[Real] V)
    (U : D →L[Real] H) (W : V →L[Real] H) (R : H →L[Real] H)
    (x : (coupledBRSTOperator A F U W R).domain) (y : WithLp 2 (D × V)) :
    inner Real (coupledBRSTOperator A F U W R x) y =
      inner Real (A x.val.fst) y.fst +
      inner Real (F ⟨x.val.snd, (coupledBRSTOperator_domain_iff A F U W R x.val).mp x.property⟩) y.snd +
      inner Real (R (U x.val.fst + W x.val.snd)) (U y.fst + W y.snd) := by
  change inner Real (coupledPhysicalBlock U W R x.val + productOperator (A.toPMap ⊤) F x) y = _
  rw [inner_add_left, coupledPhysicalBlock_pairing, productOperator_apply]
  change _ + (inner Real (A x.val.fst) y.fst + inner Real (F _) y.snd) = _
  ring

end
end JanusFormal.P0EFTJanusProgramPT12CoupledBRSTOperator4D
