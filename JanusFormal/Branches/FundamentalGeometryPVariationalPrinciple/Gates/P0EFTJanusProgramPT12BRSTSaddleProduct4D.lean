import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D

/-! The signed potential–B saddle coupled to a genuine unbounded ghost block. -/
namespace JanusFormal.P0EFTJanusProgramPT12BRSTSaddleProduct4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12SignedBRSTGram4D
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D
variable {P V G : Type*}
variable [NormedAddCommGroup P] [InnerProductSpace Real P] [CompleteSpace P]
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
variable [NormedAddCommGroup G] [InnerProductSpace Real G] [CompleteSpace G]

def nonminimalSaddle (L : P →L[Real] V) : WithLp 2 (P × V) →L[Real] WithLp 2 (P × V) :=
  signedCross (L.comp (WithLp.fstL 2 Real P V)) (WithLp.sndL 2 Real P V) -
    gram (WithLp.sndL 2 Real P V)

theorem nonminimalSaddle_pairing (L : P →L[Real] V) (x y : WithLp 2 (P × V)) :
    inner Real (nonminimalSaddle L x) y =
      inner Real (L x.fst) y.snd + inner Real x.snd (L y.fst) - inner Real x.snd y.snd := by
  simp only [nonminimalSaddle, sub_apply, inner_sub_left,
    signedCross_pairing, gram_pairing]
  rfl

theorem nonminimalSaddle_symmetric (L : P →L[Real] V) (x y : WithLp 2 (P × V)) :
    inner Real (nonminimalSaddle L x) y = inner Real x (nonminimalSaddle L y) := by
  rw [← real_inner_comm x (nonminimalSaddle L y), nonminimalSaddle_pairing,
    nonminimalSaddle_pairing]
  simp only [real_inner_comm]
  ring

def brstSaddleProduct (L : P →L[Real] V) (ghost : G →ₗ.[Real] G) :
    WithLp 2 (WithLp 2 (P × V) × G) →ₗ.[Real] WithLp 2 (WithLp 2 (P × V) × G) :=
  productOperator ((nonminimalSaddle L).toPMap ⊤) ghost

theorem brstSaddleProduct_selfAdjoint (L : P →L[Real] V) (ghost : G →ₗ.[Real] G)
    (hGhost : IsSelfAdjoint ghost) : IsSelfAdjoint (brstSaddleProduct L ghost) :=
  productOperator_selfAdjoint _ _
    (bounded_toPMap_selfAdjoint _ (nonminimalSaddle_symmetric L)) hGhost

omit [CompleteSpace G] in
theorem brstSaddleProduct_domain_iff (L : P →L[Real] V) (ghost : G →ₗ.[Real] G)
    (x : WithLp 2 (WithLp 2 (P × V) × G)) :
    x ∈ (brstSaddleProduct L ghost).domain ↔ x.snd ∈ ghost.domain := by
  rw [brstSaddleProduct, productOperator_domain_iff]
  simp

omit [CompleteSpace G] in
theorem brstSaddleProduct_pairing (L : P →L[Real] V) (ghost : G →ₗ.[Real] G)
    (x : (brstSaddleProduct L ghost).domain) (y : WithLp 2 (WithLp 2 (P × V) × G)) :
    inner Real (brstSaddleProduct L ghost x) y =
      (inner Real (L x.val.fst.fst) y.fst.snd +
        inner Real x.val.fst.snd (L y.fst.fst) - inner Real x.val.fst.snd y.fst.snd) +
      inner Real (ghost ⟨x.val.snd, (brstSaddleProduct_domain_iff L ghost x.val).mp x.property⟩) y.snd := by
  change inner Real (productOperator ((nonminimalSaddle L).toPMap ⊤) ghost x) y = _
  rw [productOperator_apply]
  change inner Real (nonminimalSaddle L x.val.fst) y.fst + _ = _
  rw [nonminimalSaddle_pairing]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12BRSTSaddleProduct4D
