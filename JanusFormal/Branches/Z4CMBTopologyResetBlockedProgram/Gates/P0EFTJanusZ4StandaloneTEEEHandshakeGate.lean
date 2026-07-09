import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4StandaloneTEEEAcquisitionGate

namespace JanusFormal
namespace P0EFTJanusZ4StandaloneTEEEHandshakeGate

set_option autoImplicit false

structure StandaloneTEEEHandshakeGate where
  standaloneHighlTEAvailable : Prop
  standaloneHighlEEAvailable : Prop
  clVsDlConventionChecked : Prop
  unitsChecked : Prop
  teSignChecked : Prop
  ellIndexingChecked : Prop
  nuisanceVectorChecked : Prop
  foregroundHandlingChecked : Prop
  grReferenceSanityChecked : Prop
  candidateFrozen : Prop
  noParameterRetuning : Prop
  noNewDeltaChannel : Prop
  noSlipOpening : Prop
  noRecombinationOpening : Prop
  noVisibilityOpening : Prop
  noMirrorSectorOpening : Prop
  noPrimordialShapeOpening : Prop
  noLensingZ4Extra : Prop
  noRawNativeToyLOS : Prop
  highlDecompositionTrialAllowed : Prop
  fullPlanckValidationAllowed : Prop
  gatePassed : Prop

def handshakeComplete (g : StandaloneTEEEHandshakeGate) : Prop :=
  g.standaloneHighlTEAvailable /\
  g.standaloneHighlEEAvailable /\
  g.clVsDlConventionChecked /\
  g.unitsChecked /\
  g.teSignChecked /\
  g.ellIndexingChecked /\
  g.nuisanceVectorChecked /\
  g.foregroundHandlingChecked /\
  g.grReferenceSanityChecked /\
  g.candidateFrozen /\
  g.noParameterRetuning /\
  g.noNewDeltaChannel /\
  g.noSlipOpening /\
  g.noRecombinationOpening /\
  g.noVisibilityOpening /\
  g.noMirrorSectorOpening /\
  g.noPrimordialShapeOpening /\
  g.noLensingZ4Extra /\
  g.noRawNativeToyLOS

def handshakeBlocked (g : StandaloneTEEEHandshakeGate) : Prop :=
  Not g.standaloneHighlTEAvailable /\
  Not g.standaloneHighlEEAvailable /\
  g.candidateFrozen /\
  g.noParameterRetuning /\
  g.noNewDeltaChannel /\
  Not g.highlDecompositionTrialAllowed /\
  Not g.fullPlanckValidationAllowed

theorem complete_handshake_allows_decomposition_trial
    (g : StandaloneTEEEHandshakeGate)
    (hPolicy : handshakeComplete g -> g.highlDecompositionTrialAllowed)
    (h : handshakeComplete g) :
    g.highlDecompositionTrialAllowed := by
  exact hPolicy h

theorem blocked_handshake_forbids_decomposition_trial
    (g : StandaloneTEEEHandshakeGate)
    (h : handshakeBlocked g) :
    Not g.highlDecompositionTrialAllowed /\ Not g.fullPlanckValidationAllowed := by
  rcases h with âŸ¨_, _, _, _, _, hNoTrial, hNoFullâŸ©
  exact âŸ¨hNoTrial, hNoFullâŸ©

end P0EFTJanusZ4StandaloneTEEEHandshakeGate
end JanusFormal
