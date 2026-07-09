namespace JanusFormal
namespace P0EFTJanusAttachedEarlyBranchC1DiagnosticGate

set_option autoImplicit false

structure AttachedEarlyBranchC1DiagnosticGate where
  earlyCoshBranchDeclared : Prop
  lateTransitionSurfaceDeclared : Prop
  c0ScaleFactorMatchPossible : Prop
  c1HubbleMatchPossible : Prop
  reachesPredragRedshift : Prop
  newTimeScaleRequired : Prop
  sourceDerived : Prop
  physicalModelReady : Prop

def attachedEarlyBranchDiagnosticReady
    (g : AttachedEarlyBranchC1DiagnosticGate) : Prop :=
  g.earlyCoshBranchDeclared /\
  g.lateTransitionSurfaceDeclared /\
  g.c0ScaleFactorMatchPossible /\
  g.c1HubbleMatchPossible /\
  g.reachesPredragRedshift /\
  g.newTimeScaleRequired /\
  Not g.sourceDerived /\
  Not g.physicalModelReady

theorem c1_attachment_is_diagnostic_not_physics
    (g : AttachedEarlyBranchC1DiagnosticGate)
    (hReady : attachedEarlyBranchDiagnosticReady g) :
    g.c1HubbleMatchPossible /\ Not g.physicalModelReady := by
  exact And.intro hReady.2.2.2.1 hReady.2.2.2.2.2.2.2

end P0EFTJanusAttachedEarlyBranchC1DiagnosticGate
end JanusFormal
