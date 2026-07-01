namespace JanusFormal
namespace P0EFTPostScreeningBAOResidual

set_option autoImplicit false

structure PostScreeningBAOResidual where
  xiBackgroundZeroAssumed : Prop
  xiGrowthLocked : Prop
  omegaMatterBackgroundScanned : Prop
  rulerScaleProfileScored : Prop
  acceptableBAOShapeFound : Prop
  backgroundMatterEqualsGrowthMatter : Prop

def postScreeningScanReady (p : PostScreeningBAOResidual) : Prop :=
  p.xiBackgroundZeroAssumed /\
  p.xiGrowthLocked /\
  p.omegaMatterBackgroundScanned /\
  p.rulerScaleProfileScored

def postScreeningBAOClosed (p : PostScreeningBAOResidual) : Prop :=
  postScreeningScanReady p /\
  p.acceptableBAOShapeFound /\
  p.backgroundMatterEqualsGrowthMatter

theorem post_screening_scan_closes_diagnostic_gate
    (p : PostScreeningBAOResidual)
    (hXiBg : p.xiBackgroundZeroAssumed)
    (hXiGrowth : p.xiGrowthLocked)
    (hOmega : p.omegaMatterBackgroundScanned)
    (hRuler : p.rulerScaleProfileScored) :
    postScreeningScanReady p := by
  exact And.intro hXiBg
    (And.intro hXiGrowth
      (And.intro hOmega hRuler))

theorem missing_bao_shape_blocks_post_screening_closure
    (p : PostScreeningBAOResidual)
    (hMissing : Not p.acceptableBAOShapeFound) :
    Not (postScreeningBAOClosed p) := by
  intro h
  exact hMissing h.right.left

theorem matter_split_blocks_post_screening_closure
    (p : PostScreeningBAOResidual)
    (hSplit : Not p.backgroundMatterEqualsGrowthMatter) :
    Not (postScreeningBAOClosed p) := by
  intro h
  exact hSplit h.right.right

end P0EFTPostScreeningBAOResidual
end JanusFormal
