import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12TwoSidedGhostAmbient4D

/-! Exact signed pairing of completed ghost features, retaining the FP defect. -/
namespace JanusFormal.P0EFTJanusProgramPT12TwoSidedGhostPairing4D

set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12TwoSidedGhostAmbient4D

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
  [NormedAddCommGroup V] [InnerProductSpace Real V]

def ghostFeatureSymmetric (field image test testImage : V) : Real :=
  (inner Real field testImage + inner Real image test) / 2

def ghostFeatureDefect (field image test testImage : V) : Real :=
  inner Real image test - inner Real field testImage

/-- Positive antighost block, negative ghost block, and the two mixed defects. -/
def twoSidedSignedGhostPairing (x y : TwoSidedGhostAmbient P V) : Real :=
  (ghostFeatureSymmetric x.fst.snd.snd.fst x.snd y.fst.snd.snd.fst y.snd -
    ghostFeatureSymmetric x.fst.snd.snd.snd.fst x.fst.snd.snd.snd.snd
      y.fst.snd.snd.snd.fst y.fst.snd.snd.snd.snd) / 2 +
  (ghostFeatureDefect x.fst.snd.snd.fst x.snd
      y.fst.snd.snd.snd.fst y.fst.snd.snd.snd.snd +
    ghostFeatureDefect y.fst.snd.snd.fst y.snd
      x.fst.snd.snd.snd.fst x.fst.snd.snd.snd.snd) / 4

theorem twoSidedSignedGhostPairing_eq_rotated (x y : TwoSidedGhostAmbient P V) :
    inner Real ((twoSidedGhostEquiv P V).symm x).fst.snd.snd.fst
        ((twoSidedGhostEquiv P V).symm y).fst.snd.snd.snd.snd +
      inner Real ((twoSidedGhostEquiv P V).symm x).fst.snd.snd.snd.snd
        ((twoSidedGhostEquiv P V).symm y).fst.snd.snd.fst =
      twoSidedSignedGhostPairing x y := by
  change inner Real ((1 / 2 : Real) • (x.fst.snd.snd.fst + x.fst.snd.snd.snd.fst))
      ((1 / 2 : Real) • (y.snd - y.fst.snd.snd.snd.snd)) +
    inner Real ((1 / 2 : Real) • (x.snd - x.fst.snd.snd.snd.snd))
      ((1 / 2 : Real) • (y.fst.snd.snd.fst + y.fst.snd.snd.snd.fst)) = _
  simp only [twoSidedSignedGhostPairing, ghostFeatureSymmetric, ghostFeatureDefect,
    real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  rw [real_inner_comm y.snd x.fst.snd.snd.snd.fst,
    real_inner_comm y.fst.snd.snd.fst x.fst.snd.snd.snd.snd]
  ring

theorem twoSidedSignedGhostPairing_comm (x y : TwoSidedGhostAmbient P V) :
    twoSidedSignedGhostPairing x y = twoSidedSignedGhostPairing y x := by
  rw [← twoSidedSignedGhostPairing_eq_rotated, ← twoSidedSignedGhostPairing_eq_rotated]
  rw [real_inner_comm ((twoSidedGhostEquiv P V).symm x).fst.snd.snd.fst,
    real_inner_comm ((twoSidedGhostEquiv P V).symm x).fst.snd.snd.snd.snd]
  exact add_comm _ _

end
end JanusFormal.P0EFTJanusProgramPT12TwoSidedGhostPairing4D
