import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4TwoSectorCarrierDegenerateArchiveGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorSourceConstructionAuditGate

set_option autoImplicit false

structure TwoSectorSourceConstructionAuditGate where
  archiveGatePassed : Prop
  plusOnlyAudited : Prop
  minusOnlyAudited : Prop
  symmetricModeAudited : Prop
  antisymmetricZ4ModeAudited : Prop
  relativeIsocurvatureAudited : Prop
  projectionOnlyAudited : Prop
  weylAudited : Prop
  theta0Audited : Prop
  piAudited : Prop
  componentSurvivalDecisionReported : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def auditReady (g : TwoSectorSourceConstructionAuditGate) : Prop :=
  g.archiveGatePassed /\
  g.plusOnlyAudited /\
  g.minusOnlyAudited /\
  g.symmetricModeAudited /\
  g.antisymmetricZ4ModeAudited /\
  g.relativeIsocurvatureAudited /\
  g.projectionOnlyAudited /\
  g.weylAudited /\
  g.theta0Audited /\
  g.piAudited /\
  g.componentSurvivalDecisionReported /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem source_construction_audit_is_pre_planck
    (g : TwoSectorSourceConstructionAuditGate)
    (hPolicy : auditReady g -> g.gatePassed)
    (h : auditReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorSourceConstructionAuditGate
end JanusFormal
