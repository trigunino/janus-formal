import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TTSWISWSolverBranch

namespace JanusFormal
namespace P0EFTJanusZ4TTSWISWPlanckGate

set_option autoImplicit false

structure TTSWISWPlanckGate where
  ttSWISWBranchSpectraUsed : Prop
  officialPlanckLikelihoodExecuted : Prop
  compressedLCDMParametersUsed : Prop
  legacyCAMBForkRequired : Prop
  planckValidationClaimed : Prop

def gateReady (g : TTSWISWPlanckGate) : Prop :=
  g.ttSWISWBranchSpectraUsed /\
  g.officialPlanckLikelihoodExecuted /\
  Not g.compressedLCDMParametersUsed /\
  Not g.legacyCAMBForkRequired

theorem gate_uses_native_branch_without_lcdm_compression
    (g : TTSWISWPlanckGate)
    (h : gateReady g) :
    g.ttSWISWBranchSpectraUsed /\ Not g.compressedLCDMParametersUsed := by
  exact And.intro h.left h.right.right.left

theorem gate_does_not_claim_planck
    (g : TTSWISWPlanckGate)
    (_h : gateReady g)
    (hNoClaim : Not g.planckValidationClaimed) :
    Not g.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4TTSWISWPlanckGate
end JanusFormal
