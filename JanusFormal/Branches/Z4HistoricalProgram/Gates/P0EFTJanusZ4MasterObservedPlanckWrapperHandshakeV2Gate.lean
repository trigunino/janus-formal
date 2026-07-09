import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshakeV2

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeV2Gate

set_option autoImplicit false

structure MasterObservedPlanckWrapperHandshakeV2Gate where
  officialLikelihoodPolicyV2Declared : Prop
  observedPlanckWrapperAvailable : Prop
  mockWrappersAllowed : Prop
  fallbackToInternalPseudoLikelihoodAllowed : Prop
  grReferenceHandshakeV2ReportPresent : Prop
  grReferenceHandshakeOnSameWrapperV2Passed : Prop
  masterV2NoRetuningReplay : Prop
  observedPlanckWrapperHandshakeV2GatePassed : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def wrapperHandshakeV2Ready (g : MasterObservedPlanckWrapperHandshakeV2Gate) : Prop :=
  g.officialLikelihoodPolicyV2Declared /\
  g.observedPlanckWrapperAvailable /\
  Not g.mockWrappersAllowed /\
  Not g.fallbackToInternalPseudoLikelihoodAllowed /\
  g.grReferenceHandshakeV2ReportPresent /\
  g.grReferenceHandshakeOnSameWrapperV2Passed /\
  Not g.masterV2NoRetuningReplay /\
  g.observedPlanckWrapperHandshakeV2GatePassed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem wrapper_handshake_v2_still_blocks_planck_until_no_retuning_replay
    (g : MasterObservedPlanckWrapperHandshakeV2Gate)
    (h : wrapperHandshakeV2Ready g) :
    g.observedPlanckWrapperHandshakeV2GatePassed /\
      Not g.masterV2NoRetuningReplay /\
      Not g.officialPlanckTrialAllowed := by
  rcases h with ⟨_, _, _, _, _, _, hNoReplay, hPassed, hNoPlanck, _, _, _, _⟩
  exact ⟨hPassed, hNoReplay, hNoPlanck⟩

end P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeV2Gate
end JanusFormal
