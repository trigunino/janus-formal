namespace JanusFormal
namespace P0EFTJanusZ2CoverMasterActionGate

set_option autoImplicit false

structure Z2CoverMasterActionGate where
  activeCoreJanusZ2Cover : Prop
  coverManifoldDeclared : Prop
  baseQuotientDeclared : Prop
  z2InvolutionDeclared : Prop
  plusSheetDerived : Prop
  minusSheetDerivedByInvolution : Prop
  masterMetricDeclared : Prop
  plusMetricProjectedFromMaster : Prop
  minusMetricProjectedFromMaster : Prop
  masterActionDeclared : Prop
  oneActionNotTwoIndependentActions : Prop
  projectedPlusEquationTargetDeclared : Prop
  projectedMinusEquationTargetDeclared : Prop
  oppositeGravitationalSignTargetDeclared : Prop
  thermodynamicDensityNotNegativeByDefinition : Prop
  rhoEffShortcutForbidden : Prop
  z4MonodromyNotAssumed : Prop
  observationalFitForbidden : Prop
  sigmaJunctionFromMasterVariationTarget : Prop
  derivationComplete : Prop

def coverMasterActionContract (g : Z2CoverMasterActionGate) : Prop :=
  g.activeCoreJanusZ2Cover /\
  g.coverManifoldDeclared /\
  g.baseQuotientDeclared /\
  g.z2InvolutionDeclared /\
  g.plusSheetDerived /\
  g.minusSheetDerivedByInvolution /\
  g.masterMetricDeclared /\
  g.plusMetricProjectedFromMaster /\
  g.minusMetricProjectedFromMaster /\
  g.masterActionDeclared /\
  g.oneActionNotTwoIndependentActions /\
  g.projectedPlusEquationTargetDeclared /\
  g.projectedMinusEquationTargetDeclared /\
  g.oppositeGravitationalSignTargetDeclared /\
  g.thermodynamicDensityNotNegativeByDefinition /\
  g.rhoEffShortcutForbidden /\
  g.z4MonodromyNotAssumed /\
  g.observationalFitForbidden /\
  g.sigmaJunctionFromMasterVariationTarget

theorem contract_keeps_single_action_and_forbids_shortcuts
    (g : Z2CoverMasterActionGate)
    (h : coverMasterActionContract g) :
    g.oneActionNotTwoIndependentActions /\
      g.rhoEffShortcutForbidden /\
      g.z4MonodromyNotAssumed /\
      g.observationalFitForbidden := by
  exact And.intro h.right.right.right.right.right.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      (And.intro h.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
        h.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left))

theorem full_derivation_requires_projection_and_junction
    (g : Z2CoverMasterActionGate)
    (h : coverMasterActionContract g)
    (_hComplete : g.derivationComplete) :
    g.projectedPlusEquationTargetDeclared /\
      g.projectedMinusEquationTargetDeclared /\
      g.sigmaJunctionFromMasterVariationTarget := by
  exact And.intro h.right.right.right.right.right.right.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.right.right.right.right.right.right.left
      h.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right)

end P0EFTJanusZ2CoverMasterActionGate
end JanusFormal
