import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusZ2SigmaSpatialVolumeProjectiveSliceGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaBackgroundCurvatureNormalizationFromBranchGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaBackgroundCurvatureBranchInputsAssemblerGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpatialVolumeInputWriterFromCurvatureBranchGate

set_option autoImplicit false

structure SpatialVolumeInputWriterFromCurvatureBranchGate where
  activeCoreZ2Sigma : Prop
  mpcToMeterConversionDeclared : Prop
  closedProjectiveBranchRequired : Prop
  curvatureBranchInputsAssemblerPassed : Prop
  inputActiveDerivedManifestIsAuthoritative : Prop
  activeCurvatureBranchInputReady : Prop
  dimensionalRCurvRequired : Prop
  dimensionlessH0ROverCInsufficientForPhysicalVolume : Prop
  nearestSpatialVolumeInputFrontierDeclared : Prop
  nearestSpatialVolumeInputFrontierDiagnosticOnly : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  spatialVolumeProjectiveSliceInputWritten : Prop
  gatePassed : Prop

def policyClosed
    (g : SpatialVolumeInputWriterFromCurvatureBranchGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.mpcToMeterConversionDeclared /\
  g.closedProjectiveBranchRequired /\
  g.dimensionalRCurvRequired /\
  g.dimensionlessH0ROverCInsufficientForPhysicalVolume /\
  g.nearestSpatialVolumeInputFrontierDeclared /\
  g.nearestSpatialVolumeInputFrontierDiagnosticOnly /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit

def gateReady
    (g : SpatialVolumeInputWriterFromCurvatureBranchGate) : Prop :=
  policyClosed g /\
  (g.inputActiveDerivedManifestIsAuthoritative \/
    g.curvatureBranchInputsAssemblerPassed) /\
  g.activeCurvatureBranchInputReady /\
  g.spatialVolumeProjectiveSliceInputWritten

theorem physical_volume_requires_dimensional_curvature_radius
    (g : SpatialVolumeInputWriterFromCurvatureBranchGate)
    (hReady : gateReady g) :
    g.dimensionalRCurvRequired := by
  exact hReady.1.2.2.2.1

theorem ready_requires_active_curvature_branch
    (g : SpatialVolumeInputWriterFromCurvatureBranchGate)
    (hReady : gateReady g) :
    g.activeCurvatureBranchInputReady := by
  exact hReady.2.2.1

theorem ready_requires_authoritative_manifest_or_curvature_branch_assembler
    (g : SpatialVolumeInputWriterFromCurvatureBranchGate)
    (hReady : gateReady g) :
    g.inputActiveDerivedManifestIsAuthoritative \/
      g.curvatureBranchInputsAssemblerPassed := by
  exact hReady.2.1

theorem diagnostic_volume_frontier_does_not_write_volume
    (g : SpatialVolumeInputWriterFromCurvatureBranchGate)
    (_hDiag : g.nearestSpatialVolumeInputFrontierDiagnosticOnly)
    (hNoBranch : Not g.activeCurvatureBranchInputReady) :
    Not (g.nearestSpatialVolumeInputFrontierDiagnosticOnly /\
      gateReady g) := by
  intro h
  exact hNoBranch h.2.2.2.1

end P0EFTJanusZ2SigmaSpatialVolumeInputWriterFromCurvatureBranchGate
end JanusFormal
