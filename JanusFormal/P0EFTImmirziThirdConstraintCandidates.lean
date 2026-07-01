namespace JanusFormal
namespace P0EFTImmirziThirdConstraintCandidates

set_option autoImplicit false

structure ImmirziThirdConstraintCandidates where
  tracelessHolstStressCandidate : Prop
  noFreeSlipGaugeCandidate : Prop
  preferredCandidateSelected : Prop
  preferredCandidateDerivedFromHolst : Prop

def thirdConstraintCandidateReady (c : ImmirziThirdConstraintCandidates) : Prop :=
  c.tracelessHolstStressCandidate /\
  c.noFreeSlipGaugeCandidate /\
  c.preferredCandidateSelected

def thirdConstraintNoFitReady (c : ImmirziThirdConstraintCandidates) : Prop :=
  thirdConstraintCandidateReady c /\
  c.preferredCandidateDerivedFromHolst

theorem candidates_select_preferred_constraint
    (c : ImmirziThirdConstraintCandidates)
    (hTrace : c.tracelessHolstStressCandidate)
    (hSlip : c.noFreeSlipGaugeCandidate)
    (hPreferred : c.preferredCandidateSelected) :
    thirdConstraintCandidateReady c := by
  exact And.intro hTrace (And.intro hSlip hPreferred)

theorem selected_but_underived_blocks_no_fit
    (c : ImmirziThirdConstraintCandidates)
    (_hReady : thirdConstraintCandidateReady c)
    (hMissing : Not c.preferredCandidateDerivedFromHolst) :
    Not (thirdConstraintNoFitReady c) := by
  intro h
  exact hMissing h.right

end P0EFTImmirziThirdConstraintCandidates
end JanusFormal
