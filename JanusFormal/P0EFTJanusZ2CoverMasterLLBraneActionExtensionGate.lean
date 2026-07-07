namespace JanusFormal
namespace P0EFTJanusZ2CoverMasterLLBraneActionExtensionGate

set_option autoImplicit false

structure Z2CoverMasterLLBraneActionExtensionGate where
  activeCoreJanusZ2Cover : Prop
  singleMasterActionRetained : Prop
  llbraneWorldvolumeAddedOnSigma : Prop
  llbraneIsExplicitExtension : Prop
  chiLLCompositeTensionDeclared : Prop
  chiLLVariationIncluded : Prop
  nullJunctionVariationIncluded : Prop
  horizonStraddlingConditionDerived : Prop
  massRadiusRelationDerived : Prop
  chiMagnitudeSelectedByGlobalVariation : Prop
  chiMagnitudeSelectedByBoundaryState : Prop
  noObservationFitForChi : Prop
  notStrictNoExtensionClosure : Prop

def llbraneExtensionContract
    (g : Z2CoverMasterLLBraneActionExtensionGate) : Prop :=
  g.activeCoreJanusZ2Cover /\
  g.singleMasterActionRetained /\
  g.llbraneWorldvolumeAddedOnSigma /\
  g.llbraneIsExplicitExtension /\
  g.chiLLCompositeTensionDeclared /\
  g.chiLLVariationIncluded /\
  g.nullJunctionVariationIncluded /\
  g.horizonStraddlingConditionDerived /\
  g.massRadiusRelationDerived /\
  g.noObservationFitForChi /\
  g.notStrictNoExtensionClosure

theorem extension_keeps_single_action_but_not_strict_no_extension
    (g : Z2CoverMasterLLBraneActionExtensionGate)
    (h : llbraneExtensionContract g) :
    g.singleMasterActionRetained /\
      g.llbraneIsExplicitExtension /\
      g.notStrictNoExtensionClosure := by
  exact And.intro h.right.left
    (And.intro h.right.right.right.left
      h.right.right.right.right.right.right.right.right.right.right)

theorem local_worldvolume_variation_does_not_select_chi_without_state
    (g : Z2CoverMasterLLBraneActionExtensionGate)
    (hNoGlobal : Not g.chiMagnitudeSelectedByGlobalVariation)
    (hNoState : Not g.chiMagnitudeSelectedByBoundaryState)
    (hClosureNeedsOne :
      g.chiMagnitudeSelectedByGlobalVariation \/
      g.chiMagnitudeSelectedByBoundaryState) :
    False := by
  cases hClosureNeedsOne with
  | inl hGlobal => exact hNoGlobal hGlobal
  | inr hState => exact hNoState hState

end P0EFTJanusZ2CoverMasterLLBraneActionExtensionGate
end JanusFormal
