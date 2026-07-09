namespace JanusFormal
namespace P0EFTJanusPredragHubbleSourceExponentMatrixGate

set_option autoImplicit false

structure PredragHubbleSourceExponentMatrixGate where
  eq40GScalesAminusOne : Prop
  eq40CSquaredScalesAminusOne : Prop
  radiationGivesHExponentMinusTwo : Prop
  matterGivesHExponentMinusThreeHalves : Prop
  curvatureGivesHExponentMinusThreeHalves : Prop
  bridgeVacuumCanGiveShallowH : Prop
  ordinaryRadiationFailsNativeDrag : Prop
  matterAndCurvatureOnlyBoundary : Prop
  bridgeVacuumOrIonizationRequired : Prop

def predragHubbleMatrixReady (g : PredragHubbleSourceExponentMatrixGate) : Prop :=
  g.eq40GScalesAminusOne /\
  g.eq40CSquaredScalesAminusOne /\
  g.radiationGivesHExponentMinusTwo /\
  g.matterGivesHExponentMinusThreeHalves /\
  g.curvatureGivesHExponentMinusThreeHalves /\
  g.bridgeVacuumCanGiveShallowH /\
  g.ordinaryRadiationFailsNativeDrag /\
  g.matterAndCurvatureOnlyBoundary /\
  g.bridgeVacuumOrIonizationRequired

theorem native_predrag_H_requires_bridge_vacuum_or_ionization
    (g : PredragHubbleSourceExponentMatrixGate)
    (hReady : predragHubbleMatrixReady g) :
    g.bridgeVacuumOrIonizationRequired := by
  exact hReady.2.2.2.2.2.2.2.2

end P0EFTJanusPredragHubbleSourceExponentMatrixGate
end JanusFormal
