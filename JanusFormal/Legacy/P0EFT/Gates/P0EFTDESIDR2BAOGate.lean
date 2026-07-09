namespace JanusFormal
namespace P0EFTDESIDR2BAOGate

set_option autoImplicit false

structure DESIDR2BAOGate where
  desiDR2BAOVectorLoaded : Prop
  desiDR2BAOCovarianceLoaded : Prop
  lcdmControlComputed : Prop
  holstGrowthBranchAvailable : Prop
  holstLateDistanceMapDerived : Prop
  holstBAOShapeDiagnosticComputed : Prop
  holstDistanceMapDerived : Prop
  holstSoundRulerMapDerived : Prop
  holstDistanceRulerMapReady : Prop
  holstBAOLikelihoodComputed : Prop

def desiBAODataReady (g : DESIDR2BAOGate) : Prop :=
  g.desiDR2BAOVectorLoaded /\
  g.desiDR2BAOCovarianceLoaded /\
  g.lcdmControlComputed

def holstBAOShapeDiagnosticReady (g : DESIDR2BAOGate) : Prop :=
  desiBAODataReady g /\
  g.holstGrowthBranchAvailable /\
  g.holstLateDistanceMapDerived /\
  g.holstBAOShapeDiagnosticComputed

def holstBAOReady (g : DESIDR2BAOGate) : Prop :=
  desiBAODataReady g /\
  g.holstGrowthBranchAvailable /\
  g.holstDistanceMapDerived /\
  g.holstSoundRulerMapDerived /\
  g.holstDistanceRulerMapReady /\
  g.holstBAOLikelihoodComputed

theorem desi_bao_loader_closes_data_gate
    (g : DESIDR2BAOGate)
    (hVector : g.desiDR2BAOVectorLoaded)
    (hCov : g.desiDR2BAOCovarianceLoaded)
    (hControl : g.lcdmControlComputed) :
    desiBAODataReady g := by
  exact And.intro hVector (And.intro hCov hControl)

theorem missing_holst_distance_map_blocks_holst_bao
    (g : DESIDR2BAOGate)
    (hMissing : Not g.holstDistanceMapDerived) :
    Not (holstBAOReady g) := by
  intro h
  exact hMissing h.right.right.left

theorem late_distance_map_allows_shape_diagnostic_only
    (g : DESIDR2BAOGate)
    (hData : desiBAODataReady g)
    (hGrowth : g.holstGrowthBranchAvailable)
    (hLateDistance : g.holstLateDistanceMapDerived)
    (hShape : g.holstBAOShapeDiagnosticComputed) :
    holstBAOShapeDiagnosticReady g := by
  exact And.intro hData (And.intro hGrowth (And.intro hLateDistance hShape))

theorem missing_holst_sound_ruler_blocks_holst_bao
    (g : DESIDR2BAOGate)
    (hMissing : Not g.holstSoundRulerMapDerived) :
    Not (holstBAOReady g) := by
  intro h
  exact hMissing h.right.right.right.left

theorem missing_unified_distance_ruler_map_blocks_holst_bao
    (g : DESIDR2BAOGate)
    (hMissing : Not g.holstDistanceRulerMapReady) :
    Not (holstBAOReady g) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTDESIDR2BAOGate
end JanusFormal
