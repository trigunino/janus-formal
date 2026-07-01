namespace JanusFormal
namespace P0EFTJanusZ4LinearizedActionVariation

set_option autoImplicit false

structure LinearizedActionVariation where
  sourceActionDensityDeclared : Prop
  plusVariationMatchesRankOneSource : Prop
  minusVariationMatchesRankOneSource : Prop
  reciprocalDeterminantWeightUsed : Prop
  linearBoundaryTermsExcluded : Prop
  nonlinearActionVariationClosed : Prop

def linearizedActionVariationReady (v : LinearizedActionVariation) : Prop :=
  v.sourceActionDensityDeclared /\
  v.plusVariationMatchesRankOneSource /\
  v.minusVariationMatchesRankOneSource /\
  v.reciprocalDeterminantWeightUsed /\
  v.linearBoundaryTermsExcluded

def fullActionVariationReady (v : LinearizedActionVariation) : Prop :=
  linearizedActionVariationReady v /\
  v.nonlinearActionVariationClosed

theorem linearized_action_does_not_close_nonlinear_action
    (v : LinearizedActionVariation)
    (_ready : linearizedActionVariationReady v)
    (hMissing : Not v.nonlinearActionVariationClosed) :
    Not (fullActionVariationReady v) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4LinearizedActionVariation
end JanusFormal
