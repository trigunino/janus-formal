namespace JanusFormal
namespace P0EFTJanusZ4CarrierParameterDegeneracyReport

set_option autoImplicit false

structure CarrierParameterDegeneracyReport where
  lambdaFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  focusParameterOmegaCDM : Prop
  combinedReferenceGainFavorable : Prop
  decomposedReferenceGainFavorable : Prop
  combinedGainSurvivesOmegaCDMMarginalization : Prop
  decomposedGainSurvivesOmegaCDMMarginalization : Prop
  profilePlanckCandidate : Prop
  fullPlanckValidation : Prop
  omegaCDMDegeneracyDetected : Prop

def omegaCDMDegeneracyDiagnostic (g : CarrierParameterDegeneracyReport) : Prop :=
  g.lambdaFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.focusParameterOmegaCDM /\
  g.combinedReferenceGainFavorable /\
  g.decomposedReferenceGainFavorable /\
  Not g.combinedGainSurvivesOmegaCDMMarginalization /\
  Not g.decomposedGainSurvivesOmegaCDMMarginalization /\
  Not g.profilePlanckCandidate /\
  Not g.fullPlanckValidation

theorem omega_cdm_degeneracy_report_blocks_promotion
    (g : CarrierParameterDegeneracyReport)
    (hPolicy : omegaCDMDegeneracyDiagnostic g -> g.omegaCDMDegeneracyDetected)
    (h : omegaCDMDegeneracyDiagnostic g) :
    g.omegaCDMDegeneracyDetected := by
  exact hPolicy h

end P0EFTJanusZ4CarrierParameterDegeneracyReport
end JanusFormal
