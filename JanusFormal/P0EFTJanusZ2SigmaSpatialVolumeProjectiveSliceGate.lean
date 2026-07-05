import JanusFormal.P0EFTJanusProjectiveTunnelVolumeRatioGate
import JanusFormal.P0EFTJanusZ2SigmaActiveFLRWSpatialMetricBranchGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpatialVolumeProjectiveSliceGate

set_option autoImplicit false

structure SpatialVolumeProjectiveSliceGate where
  activeCoreZ2Sigma : Prop
  closedProjectiveRP3VolumeFormulaReady : Prop
  finiteVolumeRequiresKPlusOne : Prop
  activeCurvatureRadiusDerived : Prop
  activeCoverSpatialMetricOrClosedRP3BranchDerived : Prop
  z2CoverFactorAppliedExactlyOnce : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  usesObservationalH0Fit : Prop
  spatialVolumeNormalizationWritten : Prop
  gatePassed : Prop

def formulaLedgerClosed
    (g : SpatialVolumeProjectiveSliceGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.closedProjectiveRP3VolumeFormulaReady /\
  g.finiteVolumeRequiresKPlusOne /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit /\
  Not g.usesObservationalH0Fit

def gateReady
    (g : SpatialVolumeProjectiveSliceGate) : Prop :=
  formulaLedgerClosed g /\
  g.activeCurvatureRadiusDerived /\
  g.activeCoverSpatialMetricOrClosedRP3BranchDerived /\
  g.z2CoverFactorAppliedExactlyOnce /\
  g.spatialVolumeNormalizationWritten

theorem ready_requires_radius_and_spatial_branch
    (g : SpatialVolumeProjectiveSliceGate)
    (hReady : gateReady g) :
    g.activeCurvatureRadiusDerived /\
      g.activeCoverSpatialMetricOrClosedRP3BranchDerived := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaSpatialVolumeProjectiveSliceGate
end JanusFormal
