namespace JanusFormal
namespace P0EFTJanusNativeBAORulerContractGate

set_option autoImplicit false

structure NativeBAORulerContractGate where
  distanceMapDeclared : Prop
  soundRulerIntegralDeclared : Prop
  dragEpochConditionDeclared : Prop
  redshiftDomainReachesDrag : Prop
  activePrimitivesAvailable : Prop
  nativeBAOContractEvaluable : Prop
  currentProxyRejected : Prop

def nativeContractFormulatedButBlocked (g : NativeBAORulerContractGate) : Prop :=
  g.distanceMapDeclared /\
  g.soundRulerIntegralDeclared /\
  g.dragEpochConditionDeclared /\
  Not g.redshiftDomainReachesDrag /\
  Not g.activePrimitivesAvailable /\
  Not g.nativeBAOContractEvaluable /\
  g.currentProxyRejected

theorem native_bao_evaluation_requires_drag_domain
    (g : NativeBAORulerContractGate)
    (h : nativeContractFormulatedButBlocked g) :
    Not g.nativeBAOContractEvaluable := by
  exact h.right.right.right.right.right.left

end P0EFTJanusNativeBAORulerContractGate
end JanusFormal
