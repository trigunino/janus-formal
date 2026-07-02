import JanusFormal.P0EFTJanusZ4ClosedBoltzmannCandidateRobustnessGate

namespace JanusFormal
namespace P0EFTJanusZ4StandaloneTEEEAcquisitionGate

set_option autoImplicit false

structure StandaloneTEEEAcquisitionGate where
  robustAvailableChannelCandidate : Prop
  standaloneHighlTEAvailable : Prop
  standaloneHighlEEAvailable : Prop
  candidateFrozenForNextTrial : Prop
  noParameterRetuning : Prop
  noNewDeltaChannel : Prop
  noSlipOpening : Prop
  noRecombinationOpening : Prop
  noVisibilityOpening : Prop
  noMirrorSectorOpening : Prop
  noPrimordialShapeOpening : Prop
  noRawNativeToyLOS : Prop
  fullHighlDecompositionTrialAllowed : Prop
  fullPlanckValidationAllowed : Prop
  gatePassed : Prop

def acquisitionReady (g : StandaloneTEEEAcquisitionGate) : Prop :=
  g.robustAvailableChannelCandidate /\
  Not g.standaloneHighlTEAvailable /\
  Not g.standaloneHighlEEAvailable /\
  g.candidateFrozenForNextTrial /\
  g.noParameterRetuning /\
  g.noNewDeltaChannel /\
  g.noSlipOpening /\
  g.noRecombinationOpening /\
  g.noVisibilityOpening /\
  g.noMirrorSectorOpening /\
  g.noPrimordialShapeOpening /\
  g.noRawNativeToyLOS /\
  Not g.fullHighlDecompositionTrialAllowed /\
  Not g.fullPlanckValidationAllowed

theorem ready_implies_acquisition_gate
    (g : StandaloneTEEEAcquisitionGate)
    (hPolicy : acquisitionReady g -> g.gatePassed)
    (h : acquisitionReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem missing_standalone_teee_blocks_full_decomposition
    (g : StandaloneTEEEAcquisitionGate)
    (h : acquisitionReady g) :
    Not g.fullHighlDecompositionTrialAllowed /\ Not g.fullPlanckValidationAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNoFullDecomp, hNoFullPlanck⟩
  exact ⟨hNoFullDecomp, hNoFullPlanck⟩

end P0EFTJanusZ4StandaloneTEEEAcquisitionGate
end JanusFormal
