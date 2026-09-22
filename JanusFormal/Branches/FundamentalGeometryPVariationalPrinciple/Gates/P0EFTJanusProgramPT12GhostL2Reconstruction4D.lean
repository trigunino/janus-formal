import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-! The bounded symmetric half-sum/half-difference ghost reconstruction on L2. -/
namespace JanusFormal.P0EFTJanusProgramPT12GhostL2Reconstruction4D
set_option autoImplicit false
noncomputable section
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Real H]

def ghostPairRotate (scale : Real) : WithLp 2 (H × H) →L[Real] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 Real H H).symm.toContinuousLinearMap.comp
    ((scale • (WithLp.fstL 2 Real H H + WithLp.sndL 2 Real H H)).prod
      (scale • (WithLp.fstL 2 Real H H - WithLp.sndL 2 Real H H)))

theorem ghostPairRotate_apply (scale : Real) (pair : WithLp 2 (H × H)) :
    ghostPairRotate H scale pair =
      WithLp.toLp 2 (scale • (pair.fst + pair.snd), scale • (pair.fst - pair.snd)) := rfl

private theorem half_full (pair : WithLp 2 (H × H)) :
    ghostPairRotate H 1 (ghostPairRotate H (1 / 2) pair) = pair := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (1 : Real) • ((1 / 2 : Real) • (pair.fst + pair.snd) +
      (1 / 2 : Real) • (pair.fst - pair.snd)) = pair.fst
    module
  · change (1 : Real) • ((1 / 2 : Real) • (pair.fst + pair.snd) -
      (1 / 2 : Real) • (pair.fst - pair.snd)) = pair.snd
    module

private theorem full_half (pair : WithLp 2 (H × H)) :
    ghostPairRotate H (1 / 2) (ghostPairRotate H 1 pair) = pair := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (1 / 2 : Real) • ((1 : Real) • (pair.fst + pair.snd) +
      (1 : Real) • (pair.fst - pair.snd)) = pair.fst
    module
  · change (1 / 2 : Real) • ((1 : Real) • (pair.fst + pair.snd) -
      (1 : Real) • (pair.fst - pair.snd)) = pair.snd
    module

def ghostL2Reconstruction : WithLp 2 (H × H) ≃L[Real] WithLp 2 (H × H) where
  toLinearEquiv :=
    { (ghostPairRotate H (1 / 2)).toLinearMap with
      invFun := ghostPairRotate H 1
      left_inv := half_full H
      right_inv := full_half H }
  continuous_toFun := (ghostPairRotate H (1 / 2)).continuous
  continuous_invFun := (ghostPairRotate H 1).continuous

theorem ghostL2Reconstruction_apply (pair : WithLp 2 (H × H)) :
    ghostL2Reconstruction H pair =
      WithLp.toLp 2 ((1 / 2 : Real) • (pair.fst + pair.snd),
        (1 / 2 : Real) • (pair.fst - pair.snd)) := rfl

theorem ghostL2Reconstruction_symmetric (first second : WithLp 2 (H × H)) :
    inner Real (ghostL2Reconstruction H first) second =
      inner Real first (ghostL2Reconstruction H second) := by
  change inner Real ((1 / 2 : Real) • (first.fst + first.snd)) second.fst +
      inner Real ((1 / 2 : Real) • (first.fst - first.snd)) second.snd =
    inner Real first.fst ((1 / 2 : Real) • (second.fst + second.snd)) +
      inner Real first.snd ((1 / 2 : Real) • (second.fst - second.snd))
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12GhostL2Reconstruction4D
