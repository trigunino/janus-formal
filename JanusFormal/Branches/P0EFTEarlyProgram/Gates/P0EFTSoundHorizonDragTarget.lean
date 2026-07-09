namespace JanusFormal
namespace P0EFTSoundHorizonDragTarget

set_option autoImplicit false

structure SoundHorizonDragTarget where
  baoFrictionRulerTargetScored : Prop
  soundHorizonShrinkEncoded : Prop
  dragEpochHubbleBoostEncoded : Prop
  dragEpochE2ExcessDerived : Prop

def soundHorizonDiagnosticReady (s : SoundHorizonDragTarget) : Prop :=
  s.baoFrictionRulerTargetScored /\
  s.soundHorizonShrinkEncoded /\
  s.dragEpochHubbleBoostEncoded

def soundHorizonNoFitReady (s : SoundHorizonDragTarget) : Prop :=
  soundHorizonDiagnosticReady s /\
  s.dragEpochE2ExcessDerived

theorem sound_horizon_drag_target_closes_diagnostic
    (s : SoundHorizonDragTarget)
    (hBAO : s.baoFrictionRulerTargetScored)
    (hRd : s.soundHorizonShrinkEncoded)
    (hH : s.dragEpochHubbleBoostEncoded) :
    soundHorizonDiagnosticReady s := by
  exact And.intro hBAO (And.intro hRd hH)

theorem missing_drag_epoch_excess_derivation_blocks_no_fit
    (s : SoundHorizonDragTarget)
    (hMissing : Not s.dragEpochE2ExcessDerived) :
    Not (soundHorizonNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTSoundHorizonDragTarget
end JanusFormal
