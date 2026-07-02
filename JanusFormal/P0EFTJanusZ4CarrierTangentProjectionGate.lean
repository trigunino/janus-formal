namespace JanusFormal
namespace P0EFTJanusZ4CarrierTangentProjectionGate

set_option autoImplicit false

structure CarrierTangentProjectionGate where
  lambdaFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  carrierTangentsComputed : Prop
  z4DeltaProjectedOntoCarrierTangent : Prop
  dominantDirectionReported : Prop
  parallelFractionReported : Prop
  perpendicularFractionReported : Prop
  orthogonalResidualTested : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  tangentProjectionDiagnosticComplete : Prop

def tangentProjectionDiagnosticReady (g : CarrierTangentProjectionGate) : Prop :=
  g.lambdaFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.carrierTangentsComputed /\
  g.z4DeltaProjectedOntoCarrierTangent /\
  g.dominantDirectionReported /\
  g.parallelFractionReported /\
  g.perpendicularFractionReported /\
  g.orthogonalResidualTested /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem tangent_projection_gate_is_diagnostic_only
    (g : CarrierTangentProjectionGate)
    (hPolicy : tangentProjectionDiagnosticReady g -> g.tangentProjectionDiagnosticComplete)
    (h : tangentProjectionDiagnosticReady g) :
    g.tangentProjectionDiagnosticComplete := by
  exact hPolicy h

end P0EFTJanusZ4CarrierTangentProjectionGate
end JanusFormal
