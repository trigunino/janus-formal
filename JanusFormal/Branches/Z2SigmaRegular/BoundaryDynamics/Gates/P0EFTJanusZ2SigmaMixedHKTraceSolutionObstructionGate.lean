import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMixedHKTraceSolutionObstructionGate

set_option autoImplicit false

structure MixedHKTraceSolutionObstructionGate where
  mixedHKVariationAllowedForDiagnostic : Prop
  finiteIsraelTraceTargetInserted : Prop
  minimalBasisTraceSystemSolved : Prop
  dirichletHOnlyMinimalCountertermCloses : Prop
  linearKTermRequired : Prop
  linearKTermCartanGHYLike : Prop
  countertermNonDuplicationPolicyDeclared : Prop
  countertermNonDuplicationPolicySatisfied : Prop
  minimalMixedHKCountertermCloses : Prop
  dirichletHOnlySelected : Prop
  mixedHKMinimalCountertermSelected : Prop
  redirectLinearKToCartanGHYOrJunction : Prop
  nonGHYDensityRequiredIfCountertermStillNeeded : Prop
  selectedRemainingRouteDeclared : Prop

def mixedHKTraceObstructionReady
    (g : MixedHKTraceSolutionObstructionGate) : Prop :=
  g.mixedHKVariationAllowedForDiagnostic /\
  g.finiteIsraelTraceTargetInserted /\
  g.minimalBasisTraceSystemSolved /\
  Not g.dirichletHOnlyMinimalCountertermCloses /\
  g.linearKTermRequired /\
  g.linearKTermCartanGHYLike /\
  g.countertermNonDuplicationPolicyDeclared /\
  Not g.dirichletHOnlySelected /\
  Not g.mixedHKMinimalCountertermSelected /\
  g.selectedRemainingRouteDeclared

theorem linear_k_duplicate_blocks_minimal_counterterm_promotion
    (g : MixedHKTraceSolutionObstructionGate)
    (hReady : mixedHKTraceObstructionReady g)
    (hDuplicate : g.linearKTermCartanGHYLike)
    (hPolicy : Not g.countertermNonDuplicationPolicySatisfied)
    (hImplies : mixedHKTraceObstructionReady g ->
      g.linearKTermCartanGHYLike ->
      Not g.countertermNonDuplicationPolicySatisfied ->
      Not g.minimalMixedHKCountertermCloses) :
    Not g.minimalMixedHKCountertermCloses := by
  exact hImplies hReady hDuplicate hPolicy

end P0EFTJanusZ2SigmaMixedHKTraceSolutionObstructionGate
end JanusFormal
