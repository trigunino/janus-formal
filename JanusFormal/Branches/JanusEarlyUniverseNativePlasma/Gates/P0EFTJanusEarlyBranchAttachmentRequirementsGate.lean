namespace JanusFormal
namespace P0EFTJanusEarlyBranchAttachmentRequirementsGate

set_option autoImplicit false

structure EarlyBranchAttachmentRequirementsGate where
  lateSNBranchTooShortForPredrag : Prop
  geometricPredragRequiresMuchSmallerAmin : Prop
  highPowerRedshiftRejectedOrUnproved : Prop
  separateEarlyBranchRequired : Prop
  matchingSurfaceRequired : Prop
  aAndHJContinuityRequired : Prop
  photonClockMapContinuityRequired : Prop
  noLateQ0RefitWithoutNewBranch : Prop
  newStateOrIntegrationConstantRequired : Prop

def earlyBranchAttachmentReady
    (g : EarlyBranchAttachmentRequirementsGate) : Prop :=
  g.lateSNBranchTooShortForPredrag /\
  g.geometricPredragRequiresMuchSmallerAmin /\
  g.highPowerRedshiftRejectedOrUnproved /\
  g.separateEarlyBranchRequired /\
  g.matchingSurfaceRequired /\
  g.aAndHJContinuityRequired /\
  g.photonClockMapContinuityRequired /\
  g.noLateQ0RefitWithoutNewBranch /\
  g.newStateOrIntegrationConstantRequired

theorem native_BAO_requires_attached_early_branch_or_derived_high_power_redshift
    (g : EarlyBranchAttachmentRequirementsGate)
    (hReady : earlyBranchAttachmentReady g) :
    g.separateEarlyBranchRequired /\ g.matchingSurfaceRequired := by
  exact And.intro hReady.2.2.2.1 hReady.2.2.2.2.1

end P0EFTJanusEarlyBranchAttachmentRequirementsGate
end JanusFormal
