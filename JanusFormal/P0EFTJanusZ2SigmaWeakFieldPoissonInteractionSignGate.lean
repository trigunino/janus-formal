namespace JanusFormal
namespace P0EFTJanusZ2SigmaWeakFieldPoissonInteractionSignGate

set_option autoImplicit false

structure WeakFieldPoissonInteractionSignGate where
  activeCoreZ2TunnelSigma : Prop
  weakFieldLimitDeclared : Prop
  twoLeafPoissonEquationsAssumed : Prop
  plusEquationSourceSigned : Prop
  minusEquationSourceSigned : Prop
  sameSectorAttractionDerived : Prop
  crossSectorRepulsionDerived : Prop
  bondiRunawayExcludedBySheetRules : Prop
  determinantRatiosSetToNewtonianLimit : Prop
  conditionalOnly : Prop
  doesNotCloseTensorBianchi : Prop
  doesNotCloseRSigmaCertificate : Prop

def weakFieldPoissonSignReductionReady
    (g : WeakFieldPoissonInteractionSignGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.weakFieldLimitDeclared /\
  g.twoLeafPoissonEquationsAssumed /\
  g.plusEquationSourceSigned /\
  g.minusEquationSourceSigned /\
  g.sameSectorAttractionDerived /\
  g.crossSectorRepulsionDerived /\
  g.bondiRunawayExcludedBySheetRules /\
  g.determinantRatiosSetToNewtonianLimit /\
  g.conditionalOnly /\
  g.doesNotCloseTensorBianchi /\
  g.doesNotCloseRSigmaCertificate

theorem weak_field_poisson_gives_interaction_signs
    (g : WeakFieldPoissonInteractionSignGate)
    (h : weakFieldPoissonSignReductionReady g) :
    g.sameSectorAttractionDerived /\ g.crossSectorRepulsionDerived := by
  exact And.intro h.right.right.right.right.right.left
    h.right.right.right.right.right.right.left

theorem weak_field_poisson_is_not_tensor_closure
    (g : WeakFieldPoissonInteractionSignGate)
    (h : weakFieldPoissonSignReductionReady g) :
    g.conditionalOnly /\ g.doesNotCloseTensorBianchi /\ g.doesNotCloseRSigmaCertificate := by
  exact And.intro h.right.right.right.right.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.right.right.right.right.left
      h.right.right.right.right.right.right.right.right.right.right.right)

end P0EFTJanusZ2SigmaWeakFieldPoissonInteractionSignGate
end JanusFormal
