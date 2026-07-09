namespace JanusFormal
namespace P0EFTJanusNativeSoundHorizonIntegralContractGate

set_option autoImplicit false

structure NativeSoundHorizonIntegralContractGate where
  rbScalesAsA : Prop
  soundSpeedContractDeclared : Prop
  soundHorizonIntegralDeclared : Prop
  smallAIntegrandExponentDeclared : Prop
  finiteFromZeroRequiresRadiationSteepH : Prop
  dragEarlyCouplingRequiresShallowH : Prop
  tensionDeclared : Prop
  nonzeroThroatLowerBoundCanResolve : Prop
  bridgeTransitionCanResolve : Prop
  numericalRulerStillBlocked : Prop

def soundHorizonContractReady
    (g : NativeSoundHorizonIntegralContractGate) : Prop :=
  g.rbScalesAsA /\
  g.soundSpeedContractDeclared /\
  g.soundHorizonIntegralDeclared /\
  g.smallAIntegrandExponentDeclared /\
  g.finiteFromZeroRequiresRadiationSteepH /\
  g.dragEarlyCouplingRequiresShallowH /\
  g.tensionDeclared /\
  g.nonzeroThroatLowerBoundCanResolve /\
  g.bridgeTransitionCanResolve /\
  g.numericalRulerStillBlocked

theorem native_ruler_needs_throat_or_transition
    (g : NativeSoundHorizonIntegralContractGate)
    (hReady : soundHorizonContractReady g) :
    g.tensionDeclared /\ g.nonzeroThroatLowerBoundCanResolve := by
  exact And.intro hReady.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.2.1

end P0EFTJanusNativeSoundHorizonIntegralContractGate
end JanusFormal
