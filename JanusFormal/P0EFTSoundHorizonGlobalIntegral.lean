namespace JanusFormal
namespace P0EFTSoundHorizonGlobalIntegral

set_option autoImplicit false

structure SoundHorizonGlobalIntegral where
  dragIntegralComputed : Prop
  deltaNeffIncluded : Prop
  rdShrinkMatchesBAOTarget : Prop
  deltaNeffGeometryDerived : Prop
  cambEarlyBackgroundImplemented : Prop

def soundHorizonIntegralReady (s : SoundHorizonGlobalIntegral) : Prop :=
  s.dragIntegralComputed /\
  s.deltaNeffIncluded /\
  s.rdShrinkMatchesBAOTarget

def cmbEarlyBackgroundReady (s : SoundHorizonGlobalIntegral) : Prop :=
  soundHorizonIntegralReady s /\
  s.deltaNeffGeometryDerived /\
  s.cambEarlyBackgroundImplemented

theorem integral_match_closes_sound_horizon_diagnostic
    (s : SoundHorizonGlobalIntegral)
    (hI : s.dragIntegralComputed)
    (hN : s.deltaNeffIncluded)
    (hR : s.rdShrinkMatchesBAOTarget) :
    soundHorizonIntegralReady s := by
  exact And.intro hI (And.intro hN hR)

theorem missing_camb_early_background_blocks_cmb_ready
    (s : SoundHorizonGlobalIntegral)
    (hMissing : Not s.cambEarlyBackgroundImplemented) :
    Not (cmbEarlyBackgroundReady s) := by
  intro h
  exact hMissing h.right.right

end P0EFTSoundHorizonGlobalIntegral
end JanusFormal
