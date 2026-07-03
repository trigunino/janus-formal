import JanusFormal.P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate
import JanusFormal.P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOSoundRulerGate

set_option autoImplicit false

structure Z2SigmaBAOSoundRulerGate where
  backgroundEquationsDerived : Prop
  photonDistanceMapDerived : Prop
  photonBaryonSoundSpeedDeclared : Prop
  dragEpochConditionDeclared : Prop
  rdIntegralOverHZ2SigmaDeclared : Prop
  fittedPlanckRdForbidden : Prop
  compressedLCDMPriorForbidden : Prop
  baoSoundRulerDerived : Prop

def baoSoundRulerLockClosed
    (g : Z2SigmaBAOSoundRulerGate) : Prop :=
  g.backgroundEquationsDerived /\
  g.photonDistanceMapDerived /\
  g.photonBaryonSoundSpeedDeclared /\
  g.dragEpochConditionDeclared /\
  g.rdIntegralOverHZ2SigmaDeclared /\
  g.fittedPlanckRdForbidden /\
  g.compressedLCDMPriorForbidden

theorem bao_sound_ruler_lock_derives_rd
    (g : Z2SigmaBAOSoundRulerGate)
    (hLock : baoSoundRulerLockClosed g)
    (hImplies : baoSoundRulerLockClosed g -> g.baoSoundRulerDerived) :
    g.baoSoundRulerDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaBAOSoundRulerGate
end JanusFormal
