namespace JanusFormal
namespace P0EFTImmirziConsistentPatchPlanckGate

set_option autoImplicit false

structure ImmirziConsistentPatchPlanckGate where
  coherentPatchRun : Prop
  improvesOverBackgroundOnly : Prop
  planckAccepted : Prop

def coherentPatchDiagnosticReady (g : ImmirziConsistentPatchPlanckGate) : Prop :=
  g.coherentPatchRun /\
  g.improvesOverBackgroundOnly

def coherentPatchNoFitReady (g : ImmirziConsistentPatchPlanckGate) : Prop :=
  coherentPatchDiagnosticReady g /\
  g.planckAccepted

theorem improvement_does_not_imply_planck_acceptance
    (g : ImmirziConsistentPatchPlanckGate)
    (hRun : g.coherentPatchRun)
    (hImprove : g.improvesOverBackgroundOnly)
    (hReject : Not g.planckAccepted) :
    coherentPatchDiagnosticReady g /\ Not (coherentPatchNoFitReady g) := by
  exact And.intro (And.intro hRun hImprove) (by intro ready; exact hReject ready.right)

end P0EFTImmirziConsistentPatchPlanckGate
end JanusFormal
