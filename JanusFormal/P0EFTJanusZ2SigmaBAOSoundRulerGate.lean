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
  baoSoundRulerFormulaReady : Prop
  hZ2SigmaNumericalReady : Prop
  photonBaryonSoundSpeedBuilderReady : Prop
  photonBaryonSoundSpeedOverCBuilderReady : Prop
  photonBaryonSoundSpeedValuesReady : Prop
  dragEpochReady : Prop
  baoSoundRulerEvaluated : Prop

def baoSoundRulerLockClosed
    (g : Z2SigmaBAOSoundRulerGate) : Prop :=
  g.backgroundEquationsDerived /\
  g.photonDistanceMapDerived /\
  g.photonBaryonSoundSpeedDeclared /\
  g.dragEpochConditionDeclared /\
  g.rdIntegralOverHZ2SigmaDeclared /\
  g.fittedPlanckRdForbidden /\
  g.compressedLCDMPriorForbidden

def baoSoundRulerEvaluationReady
    (g : Z2SigmaBAOSoundRulerGate) : Prop :=
  baoSoundRulerLockClosed g /\
  g.baoSoundRulerFormulaReady /\
  g.hZ2SigmaNumericalReady /\
  g.photonBaryonSoundSpeedValuesReady /\
  g.dragEpochReady /\
  g.baoSoundRulerEvaluated

theorem bao_sound_ruler_lock_declares_formula
    (g : Z2SigmaBAOSoundRulerGate)
    (hLock : baoSoundRulerLockClosed g)
    (hImplies : baoSoundRulerLockClosed g -> g.baoSoundRulerFormulaReady) :
    g.baoSoundRulerFormulaReady := by
  exact hImplies hLock

theorem bao_sound_ruler_evaluation_requires_numerical_background
    (g : Z2SigmaBAOSoundRulerGate)
    (hReady : baoSoundRulerEvaluationReady g) :
    g.hZ2SigmaNumericalReady := by
  exact hReady.2.2.1

end P0EFTJanusZ2SigmaBAOSoundRulerGate
end JanusFormal
