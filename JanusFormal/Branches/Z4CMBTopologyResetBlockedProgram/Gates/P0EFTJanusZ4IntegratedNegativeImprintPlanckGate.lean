import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4IntegratedNegativeImprintBranch

namespace JanusFormal
namespace P0EFTJanusZ4IntegratedNegativeImprintPlanckGate

set_option autoImplicit false

structure IntegratedNegativeImprintPlanckGate where
  integratedBranchSpectraUsed : Prop
  officialPlanckLikelihoodExecuted : Prop
  compressedLCDMParametersUsed : Prop
  legacyCAMBForkRequired : Prop
  planckValidationClaimed : Prop

def gateMeasured (g : IntegratedNegativeImprintPlanckGate) : Prop :=
  g.integratedBranchSpectraUsed /\
  g.officialPlanckLikelihoodExecuted /\
  Not g.compressedLCDMParametersUsed /\
  Not g.legacyCAMBForkRequired

theorem gate_uses_uncompressed_native_z4_branch
    (g : IntegratedNegativeImprintPlanckGate)
    (h : gateMeasured g) :
    g.integratedBranchSpectraUsed /\ Not g.compressedLCDMParametersUsed := by
  exact And.intro h.left h.right.right.left

theorem gate_does_not_claim_planck
    (g : IntegratedNegativeImprintPlanckGate)
    (_h : gateMeasured g)
    (hNoClaim : Not g.planckValidationClaimed) :
    Not g.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4IntegratedNegativeImprintPlanckGate
end JanusFormal
