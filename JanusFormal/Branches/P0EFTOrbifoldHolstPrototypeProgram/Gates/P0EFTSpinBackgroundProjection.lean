namespace JanusFormal
namespace P0EFTSpinBackgroundProjection

set_option autoImplicit false

structure SpinBackgroundProjection where
  spinGrowthProjectionLocked : Prop
  spinBackgroundProjectionDefined : Prop
  xiBackgroundScanned : Prop
  desiBAOShapeScoredForEachXi : Prop
  bestXiSelected : Prop
  xiBackgroundZeroPreferred : Prop
  geometricScreeningDerived : Prop

def projectionScanReady (p : SpinBackgroundProjection) : Prop :=
  p.spinGrowthProjectionLocked /\
  p.spinBackgroundProjectionDefined /\
  p.xiBackgroundScanned /\
  p.desiBAOShapeScoredForEachXi /\
  p.bestXiSelected

def strictPerturbativeSpinScenario (p : SpinBackgroundProjection) : Prop :=
  projectionScanReady p /\
  p.xiBackgroundZeroPreferred

def noFitProjectionReady (p : SpinBackgroundProjection) : Prop :=
  strictPerturbativeSpinScenario p /\
  p.geometricScreeningDerived

theorem scan_closes_projection_diagnostic
    (p : SpinBackgroundProjection)
    (hGrowth : p.spinGrowthProjectionLocked)
    (hBg : p.spinBackgroundProjectionDefined)
    (hScan : p.xiBackgroundScanned)
    (hScore : p.desiBAOShapeScoredForEachXi)
    (hBest : p.bestXiSelected) :
    projectionScanReady p := by
  exact And.intro hGrowth
    (And.intro hBg
      (And.intro hScan
        (And.intro hScore hBest)))

theorem missing_geometric_screening_blocks_no_fit_projection
    (p : SpinBackgroundProjection)
    (hMissing : Not p.geometricScreeningDerived) :
    Not (noFitProjectionReady p) := by
  intro h
  exact hMissing h.right

end P0EFTSpinBackgroundProjection
end JanusFormal
