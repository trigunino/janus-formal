namespace JanusFormal
namespace P0EFTJanusDirectCMBGate

set_option autoImplicit false

structure JanusDirectCMBGate where
  holstGrowthBranchAvailable : Prop
  usesLCDMCompressedPlanckParametersAsVerdict : Prop
  janusAngularDiameterDistanceDerived : Prop
  janusSoundRulerDerived : Prop
  janusDistanceRulerMapReady : Prop
  janusTransferFunctionsDerived : Prop
  cmbSpectraComputed : Prop
  directCMBLikelihoodReady : Prop

def janusDistanceRulerReady (g : JanusDirectCMBGate) : Prop :=
  g.janusAngularDiameterDistanceDerived /\
  g.janusSoundRulerDerived

def directCMBReady (g : JanusDirectCMBGate) : Prop :=
  g.holstGrowthBranchAvailable /\
  Not g.usesLCDMCompressedPlanckParametersAsVerdict /\
  janusDistanceRulerReady g /\
  g.janusDistanceRulerMapReady /\
  g.janusTransferFunctionsDerived /\
  g.cmbSpectraComputed /\
  g.directCMBLikelihoodReady

theorem missing_janus_distance_blocks_direct_cmb
    (g : JanusDirectCMBGate)
    (hMissing : Not g.janusAngularDiameterDistanceDerived) :
    Not (directCMBReady g) := by
  intro h
  exact hMissing h.right.right.left.left

theorem missing_janus_sound_ruler_blocks_direct_cmb
    (g : JanusDirectCMBGate)
    (hMissing : Not g.janusSoundRulerDerived) :
    Not (directCMBReady g) := by
  intro h
  exact hMissing h.right.right.left.right

theorem lcdm_compressed_verdict_forbidden_for_direct_cmb
    (g : JanusDirectCMBGate)
    (hBad : g.usesLCDMCompressedPlanckParametersAsVerdict) :
    Not (directCMBReady g) := by
  intro h
  exact h.right.left hBad

theorem missing_unified_distance_ruler_map_blocks_direct_cmb
    (g : JanusDirectCMBGate)
    (hMissing : Not g.janusDistanceRulerMapReady) :
    Not (directCMBReady g) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTJanusDirectCMBGate
end JanusFormal
