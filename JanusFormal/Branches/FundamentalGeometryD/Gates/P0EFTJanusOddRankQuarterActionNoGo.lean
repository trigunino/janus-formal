import Mathlib

namespace JanusFormal
namespace P0EFTJanusOddRankQuarterActionNoGo

set_option autoImplicit false

/-- A real representation made only of genuine quarter-turn planes. -/
structure PureQuarterRealRepresentation where
  realRank : ℕ
  quarterPlaneCount : ℕ
  rankDecomposition : realRank = 2 * quarterPlaneCount

/-- Every such real rank is even. -/
theorem pure_quarter_real_rank_even
    (s : PureQuarterRealRepresentation) :
    Even s.realRank := by
  exact ⟨s.quarterPlaneCount, s.rankDecomposition⟩

/-- There is no pure quarter-turn representation of real rank five. -/
theorem no_pure_quarter_real_rank_five :
    Not (∃ s : PureQuarterRealRepresentation,
      s.realRank = 5) := by
  rintro ⟨s, hRank⟩
  have hEven := pure_quarter_real_rank_even s
  rw [hRank] at hEven
  norm_num at hEven

/-- Complex rank five has underlying real rank ten. -/
def realRankOfComplexRank (complexRank : ℕ) : ℕ :=
  2 * complexRank

@[simp] theorem complex_rank_five_has_real_rank_ten :
    realRankOfComplexRank 5 = 10 := by
  norm_num [realRankOfComplexRank]

/-- A rank-ten real sector can consist of five quarter-turn planes. -/
def fivePlaneQuarterRepresentation : PureQuarterRealRepresentation :=
  { realRank := 10
    quarterPlaneCount := 5
    rankDecomposition := by norm_num }

@[simp] theorem five_plane_representation_rank :
    fivePlaneQuarterRepresentation.realRank = 10 := by
  rfl

@[simp] theorem five_plane_representation_weight :
    fivePlaneQuarterRepresentation.quarterPlaneCount = 5 := by
  rfl

/--
Consequently the real rank-five traceless tensor bundle on one fold cannot
itself carry an everywhere pure quarter-turn complex structure.  One must
complexify it, pair it with a second real rank-five sector, or introduce a
different higher-rank internal bundle.  Each option changes the descent and
determinant multiplicity bookkeeping.
-/
structure OddRankQuarterExitStatus where
  oneFoldTracelessRankFiveDerived : Prop
  directRealQuarterActionRejected : Prop
  complexificationConstructed : Prop
  secondRealCopyConstructed : Prop
  higherRankInternalBundleConstructed : Prop
  selectedExitDescentLawDerived : Prop
  determinantMultiplicityRecomputed : Prop


def oddRankQuarterExitClosed
    (s : OddRankQuarterExitStatus) : Prop :=
  s.oneFoldTracelessRankFiveDerived /\
  s.directRealQuarterActionRejected /\
  (s.complexificationConstructed \/
    s.secondRealCopyConstructed \/
    s.higherRankInternalBundleConstructed) /\
  s.selectedExitDescentLawDerived /\
  s.determinantMultiplicityRecomputed

end P0EFTJanusOddRankQuarterActionNoGo
end JanusFormal
