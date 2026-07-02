import JanusFormal.P0EFTJanusZ4DerivedSlipSourceLevelRegenerationGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipCarrierTangentProjectionGate

set_option autoImplicit false

structure DerivedSlipCarrierTangentProjectionGate where
  sourceLevelRegenerationGatePassed : Prop
  visibleSlipProjectionDeclared : Prop
  orientationSignPolicyDeclared : Prop
  orientationFlipDiagnosticOnly : Prop
  carrierTangentsComputed : Prop
  surfaceTermProjected : Prop
  earlyISWTermProjected : Prop
  polarizationPiTermProjected : Prop
  fullSlipSourceProjected : Prop
  oldNoSlipReferenceReported : Prop
  parallelFractionReported : Prop
  perpendicularFractionReported : Prop
  dominantDirectionReported : Prop
  interpretationBandReported : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def diagnosticReady (g : DerivedSlipCarrierTangentProjectionGate) : Prop :=
  g.sourceLevelRegenerationGatePassed /\
  g.visibleSlipProjectionDeclared /\
  g.orientationSignPolicyDeclared /\
  g.orientationFlipDiagnosticOnly /\
  g.carrierTangentsComputed /\
  g.surfaceTermProjected /\
  g.earlyISWTermProjected /\
  g.polarizationPiTermProjected /\
  g.fullSlipSourceProjected /\
  g.oldNoSlipReferenceReported /\
  g.parallelFractionReported /\
  g.perpendicularFractionReported /\
  g.dominantDirectionReported /\
  g.interpretationBandReported /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem derived_slip_tangent_projection_is_diagnostic_only
    (g : DerivedSlipCarrierTangentProjectionGate)
    (hPolicy : diagnosticReady g -> g.gatePassed)
    (h : diagnosticReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipCarrierTangentProjectionGate
end JanusFormal
