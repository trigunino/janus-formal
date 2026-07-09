namespace JanusFormal
namespace P0EFTJanusNativeDragExponentFrontierGate

set_option autoImplicit false

structure NativeDragExponentFrontierGate where
  conservedElectronNumberGivesNEAminus3 : Prop
  eq40ThomsonAreaScalesA2 : Prop
  eq40LightSpeedScalesAminusHalf : Prop
  dragRateExponentAminusThreeHalf : Prop
  gammaOverHExponentDeclared : Prop
  radiationLikeHTooSteep : Prop
  variableGRadiationLikeHTooSteep : Prop
  requiredHRegimeDeclared : Prop
  alphaFittingCannotRepairDragExponent : Prop
  nativeHJorIonizationRequired : Prop

def nativeDragFrontierReady (g : NativeDragExponentFrontierGate) : Prop :=
  g.conservedElectronNumberGivesNEAminus3 /\
  g.eq40ThomsonAreaScalesA2 /\
  g.eq40LightSpeedScalesAminusHalf /\
  g.dragRateExponentAminusThreeHalf /\
  g.gammaOverHExponentDeclared /\
  g.radiationLikeHTooSteep /\
  g.variableGRadiationLikeHTooSteep /\
  g.requiredHRegimeDeclared /\
  g.alphaFittingCannotRepairDragExponent /\
  g.nativeHJorIonizationRequired

theorem native_drag_requires_HJ_or_ionization
    (g : NativeDragExponentFrontierGate)
    (hReady : nativeDragFrontierReady g) :
    g.nativeHJorIonizationRequired /\ g.alphaFittingCannotRepairDragExponent := by
  exact And.intro hReady.2.2.2.2.2.2.2.2.2 hReady.2.2.2.2.2.2.2.2.1

end P0EFTJanusNativeDragExponentFrontierGate
end JanusFormal
