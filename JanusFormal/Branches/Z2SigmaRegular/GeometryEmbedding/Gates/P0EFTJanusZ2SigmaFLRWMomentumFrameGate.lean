import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWMomentumFrameGate

set_option autoImplicit false

structure FLRWMomentumFrameGate where
  flrwMomentumFrameBibliographyChecked : Prop
  coframeConnectionPullbackGateDeclared : Prop
  radialEnergyDispersionGateDeclared : Prop
  plusOrthonormalFrameDeclared : Prop
  minusOrthonormalFrameDeclared : Prop
  comovingObserverFrameDeclared : Prop
  physicalMomentumDeclared : Prop
  comovingMomentumDeclared : Prop
  isotropicMomentumNormDeclared : Prop
  observationalFitForbidden : Prop
  plusCoframePullbackReady : Prop
  minusCoframePullbackReady : Prop
  plusComovingObserverFrameDerived : Prop
  minusComovingObserverFrameDerived : Prop
  plusMomentumNormDerived : Prop
  minusMomentumNormDerived : Prop
  plusFLRWMomentumFrameDerived : Prop
  minusFLRWMomentumFrameDerived : Prop
  projectedFLRWMomentumFrameDerived : Prop
  flrwMomentumFrameReady : Prop

def flrwMomentumFrameLedgerDeclared
    (g : FLRWMomentumFrameGate) : Prop :=
  g.flrwMomentumFrameBibliographyChecked /\
  g.coframeConnectionPullbackGateDeclared /\
  g.radialEnergyDispersionGateDeclared /\
  g.plusOrthonormalFrameDeclared /\
  g.minusOrthonormalFrameDeclared /\
  g.comovingObserverFrameDeclared /\
  g.physicalMomentumDeclared /\
  g.comovingMomentumDeclared /\
  g.isotropicMomentumNormDeclared /\
  g.observationalFitForbidden

def flrwMomentumFrameReady
    (g : FLRWMomentumFrameGate) : Prop :=
  flrwMomentumFrameLedgerDeclared g /\
  g.plusCoframePullbackReady /\
  g.minusCoframePullbackReady /\
  g.plusComovingObserverFrameDerived /\
  g.minusComovingObserverFrameDerived /\
  g.plusMomentumNormDerived /\
  g.minusMomentumNormDerived /\
  g.plusFLRWMomentumFrameDerived /\
  g.minusFLRWMomentumFrameDerived /\
  g.projectedFLRWMomentumFrameDerived /\
  g.flrwMomentumFrameReady

theorem flrw_momentum_frame_requires_projected_frame
    (g : FLRWMomentumFrameGate)
    (hReady : flrwMomentumFrameReady g) :
    g.projectedFLRWMomentumFrameDerived := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, _, hProjectedFrame, _⟩
  exact hProjectedFrame

end P0EFTJanusZ2SigmaFLRWMomentumFrameGate
end JanusFormal
