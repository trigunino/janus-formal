namespace JanusFormal
namespace P0EFTJanusHolstDistanceRulerMap

set_option autoImplicit false

structure JanusHolstDistanceRulerMap where
  holstRadionBackgroundStressDerived : Prop
  earlyRadiationBranchDerived : Prop
  HJanusHolstDerived : Prop
  radialDistanceDerived : Prop
  transverseDistanceDerived : Prop
  volumeDistanceDerived : Prop
  soundRulerDerived : Prop
  recombinationMapDerived : Prop
  thetaStarDerived : Prop
  usesLCDMBackgroundShortcut : Prop
  arbitraryBAORulerFit : Prop

def backgroundReady (m : JanusHolstDistanceRulerMap) : Prop :=
  m.holstRadionBackgroundStressDerived /\
  m.earlyRadiationBranchDerived /\
  m.HJanusHolstDerived

def lateDistanceMapReady (m : JanusHolstDistanceRulerMap) : Prop :=
  backgroundReady m /\
  m.radialDistanceDerived /\
  m.transverseDistanceDerived /\
  m.volumeDistanceDerived /\
  Not m.usesLCDMBackgroundShortcut

def baoDistanceRulerReady (m : JanusHolstDistanceRulerMap) : Prop :=
  backgroundReady m /\
  m.radialDistanceDerived /\
  m.transverseDistanceDerived /\
  m.volumeDistanceDerived /\
  m.soundRulerDerived /\
  Not m.usesLCDMBackgroundShortcut /\
  Not m.arbitraryBAORulerFit

def cmbDistanceRulerReady (m : JanusHolstDistanceRulerMap) : Prop :=
  backgroundReady m /\
  m.transverseDistanceDerived /\
  m.soundRulerDerived /\
  m.recombinationMapDerived /\
  m.thetaStarDerived /\
  Not m.usesLCDMBackgroundShortcut

theorem missing_H_blocks_bao_distance_ruler
    (m : JanusHolstDistanceRulerMap)
    (hMissing : Not m.HJanusHolstDerived) :
    Not (baoDistanceRulerReady m) := by
  intro h
  exact hMissing h.left.right.right

theorem late_distance_map_closes_shape_diagnostic_gate
    (m : JanusHolstDistanceRulerMap)
    (hBackground : backgroundReady m)
    (hRadial : m.radialDistanceDerived)
    (hTransverse : m.transverseDistanceDerived)
    (hVolume : m.volumeDistanceDerived)
    (hNoLCDM : Not m.usesLCDMBackgroundShortcut) :
    lateDistanceMapReady m := by
  exact And.intro hBackground
    (And.intro hRadial
      (And.intro hTransverse
        (And.intro hVolume hNoLCDM)))

theorem missing_sound_ruler_blocks_bao
    (m : JanusHolstDistanceRulerMap)
    (hMissing : Not m.soundRulerDerived) :
    Not (baoDistanceRulerReady m) := by
  intro h
  exact hMissing h.right.right.right.right.left

theorem lcdm_background_shortcut_blocks_bao
    (m : JanusHolstDistanceRulerMap)
    (hShortcut : m.usesLCDMBackgroundShortcut) :
    Not (baoDistanceRulerReady m) := by
  intro h
  exact h.right.right.right.right.right.left hShortcut

theorem arbitrary_ruler_fit_blocks_bao
    (m : JanusHolstDistanceRulerMap)
    (hFit : m.arbitraryBAORulerFit) :
    Not (baoDistanceRulerReady m) := by
  intro h
  exact h.right.right.right.right.right.right hFit

theorem missing_theta_star_blocks_cmb
    (m : JanusHolstDistanceRulerMap)
    (hMissing : Not m.thetaStarDerived) :
    Not (cmbDistanceRulerReady m) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTJanusHolstDistanceRulerMap
end JanusFormal
