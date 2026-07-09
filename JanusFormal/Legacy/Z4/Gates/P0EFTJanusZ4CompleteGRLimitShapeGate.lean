import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4CompleteCMBSolverStack

namespace JanusFormal
namespace P0EFTJanusZ4CompleteGRLimitShapeGate

set_option autoImplicit false

structure CompleteGRLimitShapeGate where
  z4Enabled : Prop
  nativeGRLimitSolverExecuted : Prop
  cambGRReferenceGenerated : Prop
  grLimitShapePassed : Prop
  z4OnPlanckInterpretationAllowed : Prop
  candidatePromotionAllowed : Prop
  fullPlanckValidation : Prop

def blockedByGRLimitMismatch (g : CompleteGRLimitShapeGate) : Prop :=
  Not g.z4Enabled /\
  g.nativeGRLimitSolverExecuted /\
  g.cambGRReferenceGenerated /\
  Not g.grLimitShapePassed /\
  Not g.z4OnPlanckInterpretationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.fullPlanckValidation

theorem gr_limit_mismatch_blocks_planck_interpretation
    (g : CompleteGRLimitShapeGate)
    (h : blockedByGRLimitMismatch g) :
    Not g.z4OnPlanckInterpretationAllowed /\ Not g.fullPlanckValidation := by
  rcases h with ⟨_, _, _, _, hInterpretation, _, hFull⟩
  exact ⟨hInterpretation, hFull⟩

end P0EFTJanusZ4CompleteGRLimitShapeGate
end JanusFormal
