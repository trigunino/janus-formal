import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! Bounded ghost rotation when both FP graph coordinates are retained. -/
namespace JanusFormal.P0EFTJanusProgramPT12TwoSidedGhostAmbient4D

set_option autoImplicit false
noncomputable section

variable (P V : Type*) [NormedAddCommGroup P] [NormedSpace Real P]
  [NormedAddCommGroup V] [NormedSpace Real V]

abbrev GhostTail3 := WithLp 2 (V × V)
abbrev GhostTail2 := WithLp 2 (V × GhostTail3 V)
abbrev GhostTail1 := WithLp 2 (V × GhostTail2 V)
abbrev GhostOldAmbient := WithLp 2 (P × GhostTail1 V)
abbrev TwoSidedGhostAmbient := WithLp 2 (GhostOldAmbient P V × V)

private def pairL {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup G] [NormedSpace Real G]
    (first : E →L[Real] F) (second : E →L[Real] G) : E →L[Real] WithLp 2 (F × G) :=
  (WithLp.prodContinuousLinearEquiv 2 Real F G).symm.toContinuousLinearMap.comp
    (first.prod second)

/-- Passive fields and B are fixed; both the fields and their FP features rotate. -/
def twoSidedGhostRotate (scale : Real) :
    TwoSidedGhostAmbient P V →L[Real] TwoSidedGhostAmbient P V := by
  let old : TwoSidedGhostAmbient P V →L[Real] GhostOldAmbient P V := WithLp.fstL 2 Real _ _
  let antiFP : TwoSidedGhostAmbient P V →L[Real] V := WithLp.sndL 2 Real _ _
  let passive := (WithLp.fstL 2 Real P (GhostTail1 V)).comp old
  let tail1 := (WithLp.sndL 2 Real P (GhostTail1 V)).comp old
  let auxiliary := (WithLp.fstL 2 Real V (GhostTail2 V)).comp tail1
  let tail2 := (WithLp.sndL 2 Real V (GhostTail2 V)).comp tail1
  let anti := (WithLp.fstL 2 Real V (GhostTail3 V)).comp tail2
  let tail3 := (WithLp.sndL 2 Real V (GhostTail3 V)).comp tail2
  let ghost := (WithLp.fstL 2 Real V V).comp tail3
  let ghostFP := (WithLp.sndL 2 Real V V).comp tail3
  exact pairL
    (pairL passive (pairL auxiliary (pairL (scale • (anti + ghost))
      (pairL (scale • (anti - ghost)) (scale • (antiFP - ghostFP))))))
    (scale • (antiFP + ghostFP))

theorem twoSidedGhostRotate_apply (scale : Real) (x : TwoSidedGhostAmbient P V) :
    twoSidedGhostRotate P V scale x =
      WithLp.toLp 2
        (WithLp.toLp 2 (x.fst.fst, WithLp.toLp 2
          (x.fst.snd.fst, WithLp.toLp 2
            (scale • (x.fst.snd.snd.fst + x.fst.snd.snd.snd.fst), WithLp.toLp 2
              (scale • (x.fst.snd.snd.fst - x.fst.snd.snd.snd.fst),
                scale • (x.snd - x.fst.snd.snd.snd.snd))))),
          scale • (x.snd + x.fst.snd.snd.snd.snd)) := rfl

private theorem rotate_inverse (x : TwoSidedGhostAmbient P V) :
    twoSidedGhostRotate P V (1 / 2) (twoSidedGhostRotate P V 1 x) = x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · rfl
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · change (1 / 2 : Real) • ((1 : Real) • (x.fst.snd.snd.fst + x.fst.snd.snd.snd.fst) + (1 : Real) • (x.fst.snd.snd.fst - x.fst.snd.snd.snd.fst)) = x.fst.snd.snd.fst
          module
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · change (1 / 2 : Real) • ((1 : Real) • (x.fst.snd.snd.fst + x.fst.snd.snd.snd.fst) - (1 : Real) • (x.fst.snd.snd.fst - x.fst.snd.snd.snd.fst)) = x.fst.snd.snd.snd.fst
            module
          · change (1 / 2 : Real) • ((1 : Real) • (x.snd + x.fst.snd.snd.snd.snd) - (1 : Real) • (x.snd - x.fst.snd.snd.snd.snd)) = x.fst.snd.snd.snd.snd
            module
  · change (1 / 2 : Real) • ((1 : Real) • (x.snd + x.fst.snd.snd.snd.snd) + (1 : Real) • (x.snd - x.fst.snd.snd.snd.snd)) = x.snd
    module

private theorem inverse_rotate (x : TwoSidedGhostAmbient P V) :
    twoSidedGhostRotate P V 1 (twoSidedGhostRotate P V (1 / 2) x) = x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · rfl
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · change (1 : Real) • ((1 / 2 : Real) • (x.fst.snd.snd.fst + x.fst.snd.snd.snd.fst) + (1 / 2 : Real) • (x.fst.snd.snd.fst - x.fst.snd.snd.snd.fst)) = x.fst.snd.snd.fst
          module
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · change (1 : Real) • ((1 / 2 : Real) • (x.fst.snd.snd.fst + x.fst.snd.snd.snd.fst) - (1 / 2 : Real) • (x.fst.snd.snd.fst - x.fst.snd.snd.snd.fst)) = x.fst.snd.snd.snd.fst
            module
          · change (1 : Real) • ((1 / 2 : Real) • (x.snd + x.fst.snd.snd.snd.snd) - (1 / 2 : Real) • (x.snd - x.fst.snd.snd.snd.snd)) = x.fst.snd.snd.snd.snd
            module
  · change (1 : Real) • ((1 / 2 : Real) • (x.snd + x.fst.snd.snd.snd.snd) + (1 / 2 : Real) • (x.snd - x.fst.snd.snd.snd.snd)) = x.snd
    module

def twoSidedGhostEquiv : TwoSidedGhostAmbient P V ≃L[Real] TwoSidedGhostAmbient P V where
  toLinearEquiv :=
    { (twoSidedGhostRotate P V 1).toLinearMap with
      invFun := twoSidedGhostRotate P V (1 / 2)
      left_inv := rotate_inverse P V
      right_inv := inverse_rotate P V }
  continuous_toFun := (twoSidedGhostRotate P V 1).continuous
  continuous_invFun := (twoSidedGhostRotate P V (1 / 2)).continuous

end
end JanusFormal.P0EFTJanusProgramPT12TwoSidedGhostAmbient4D
