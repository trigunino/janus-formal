import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaRP3SpatialSliceCurvatureSignGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRP3SpatialSliceInputWriterFromProjectiveFoliationGate

set_option autoImplicit false

structure RP3SpatialSliceInputWriterFromProjectiveFoliationGate where
  activeCoreZ2Sigma : Prop
  ambientCoverS4 : Prop
  ambientQuotientRP4 : Prop
  spatialCoverLeafS3 : Prop
  spatialQuotientLeafRP3 : Prop
  antipodalActionPreservesSpatialLeaf : Prop
  spatialLeafActionFree : Prop
  flrwSlicesIdentifiedWithSpatialLeaves : Prop
  projectiveFoliationToRP3SliceRuleReady : Prop
  requiresActiveFoliationNotTopologyAlone : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  rp3SpatialSliceInputWritten : Prop
  curvatureRadiusStillRequired : Prop
  omegaKNotComputedHere : Prop
  gatePassed : Prop

def foliationPolicyClosed
    (g : RP3SpatialSliceInputWriterFromProjectiveFoliationGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.ambientCoverS4 /\
  g.ambientQuotientRP4 /\
  g.spatialCoverLeafS3 /\
  g.spatialQuotientLeafRP3 /\
  g.antipodalActionPreservesSpatialLeaf /\
  g.spatialLeafActionFree /\
  g.flrwSlicesIdentifiedWithSpatialLeaves /\
  g.projectiveFoliationToRP3SliceRuleReady /\
  g.requiresActiveFoliationNotTopologyAlone /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit /\
  g.curvatureRadiusStillRequired /\
  g.omegaKNotComputedHere

theorem foliation_rule_requires_active_leaf_identification
    (g : RP3SpatialSliceInputWriterFromProjectiveFoliationGate)
    (h : foliationPolicyClosed g) :
    g.flrwSlicesIdentifiedWithSpatialLeaves := by
  exact h.2.2.2.2.2.2.2.1

theorem writer_does_not_compute_omega_k
    (g : RP3SpatialSliceInputWriterFromProjectiveFoliationGate)
    (h : foliationPolicyClosed g) :
    g.omegaKNotComputedHere := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem gate_pass_requires_rp3_input_written
    (g : RP3SpatialSliceInputWriterFromProjectiveFoliationGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.rp3SpatialSliceInputWritten) :
    g.rp3SpatialSliceInputWritten := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaRP3SpatialSliceInputWriterFromProjectiveFoliationGate
end JanusFormal
