namespace JanusFormal
namespace P0EFTJanusProjectiveTunnelVolumeRatioGate

set_option autoImplicit false

structure ProjectiveTunnelVolumeRatioGate where
  twoFoldCoverSurvivesTunnelSurgery : Prop
  deckInvariantVolumeFormDeclared : Prop
  quotientMeasureDescends : Prop
  coverDegreeEqualsTwo : Prop
  coverToQuotientVolumeRatioTwo : Prop
  ratioUniqueByCoverDegree : Prop
  phenomenologicalSheetSplitInferred : Prop

def projectiveTunnelCoverVolumeRatioClosed
    (g : ProjectiveTunnelVolumeRatioGate) : Prop :=
  g.twoFoldCoverSurvivesTunnelSurgery /\
  g.deckInvariantVolumeFormDeclared /\
  g.quotientMeasureDescends /\
  g.coverDegreeEqualsTwo /\
  g.coverToQuotientVolumeRatioTwo /\
  g.ratioUniqueByCoverDegree /\
  Not g.phenomenologicalSheetSplitInferred

theorem twofold_cover_degree_fixes_cover_volume_ratio
    (g : ProjectiveTunnelVolumeRatioGate)
    (h : projectiveTunnelCoverVolumeRatioClosed g) :
    g.coverToQuotientVolumeRatioTwo /\ g.ratioUniqueByCoverDegree := by
  exact And.intro h.2.2.2.2.1 h.2.2.2.2.2.1

theorem cover_ratio_does_not_infer_phenomenological_sheet_split
    (g : ProjectiveTunnelVolumeRatioGate)
    (h : projectiveTunnelCoverVolumeRatioClosed g) :
    Not g.phenomenologicalSheetSplitInferred := by
  exact h.2.2.2.2.2.2

end P0EFTJanusProjectiveTunnelVolumeRatioGate
end JanusFormal
