import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TwoSectorSourceConstructionAuditGate

namespace JanusFormal
namespace P0EFTJanusZ4ProjectionParityPreservationGate

set_option autoImplicit false

structure ProjectionParityPreservationGate where
  sourceConstructionAuditPassed : Prop
  valueProjectionTested : Prop
  normalDerivativeProjectionTested : Prop
  jumpProjectionTested : Prop
  membraneWeightedProjectionTested : Prop
  mixedValueDerivativeProjectionTested : Prop
  symmetricProjectionNormReported : Prop
  antisymmetricProjectionNormReported : Prop
  antisymmetricSurvivalRatioReported : Prop
  carrierTangencyReported : Prop
  preservingProjectionDecisionReported : Prop
  freeProjectionCoefficientAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def parityAuditReady (g : ProjectionParityPreservationGate) : Prop :=
  g.sourceConstructionAuditPassed /\
  g.valueProjectionTested /\
  g.normalDerivativeProjectionTested /\
  g.jumpProjectionTested /\
  g.membraneWeightedProjectionTested /\
  g.mixedValueDerivativeProjectionTested /\
  g.symmetricProjectionNormReported /\
  g.antisymmetricProjectionNormReported /\
  g.antisymmetricSurvivalRatioReported /\
  g.carrierTangencyReported /\
  g.preservingProjectionDecisionReported /\
  Not g.freeProjectionCoefficientAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem projection_parity_preservation_is_pre_observational
    (g : ProjectionParityPreservationGate)
    (hPolicy : parityAuditReady g -> g.gatePassed)
    (h : parityAuditReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4ProjectionParityPreservationGate
end JanusFormal
