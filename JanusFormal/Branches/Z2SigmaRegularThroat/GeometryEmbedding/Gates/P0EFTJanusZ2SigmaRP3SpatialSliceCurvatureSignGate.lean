import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelCoverRatioGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveCurvatureSignGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRP3SpatialSliceCurvatureSignGate

set_option autoImplicit false

structure RP3SpatialSliceCurvatureSignGate where
  activeCoreZ2Sigma : Prop
  coverSpatialSliceS3 : Prop
  quotientSpatialSliceRP3 : Prop
  antipodalZ2Quotient : Prop
  rp3SpatialSliceToKPlusOneRuleReady : Prop
  topologyAloneFixesNumericOmegaK : Prop
  curvatureRadiusStillRequired : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  usesObservationalCurvatureFit : Prop
  curvatureSignInputWritten : Prop
  gatePassed : Prop

def policyClosed
    (g : RP3SpatialSliceCurvatureSignGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.coverSpatialSliceS3 /\
  g.quotientSpatialSliceRP3 /\
  g.antipodalZ2Quotient /\
  g.rp3SpatialSliceToKPlusOneRuleReady /\
  Not g.topologyAloneFixesNumericOmegaK /\
  g.curvatureRadiusStillRequired /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background /\
  Not g.usesObservationalCurvatureFit

theorem rp3_sign_rule_does_not_close_radius
    (g : RP3SpatialSliceCurvatureSignGate)
    (h : policyClosed g) :
    g.curvatureRadiusStillRequired := by
  rcases h with ⟨_, _, _, _, _, _, hRadius, _, _, _⟩
  exact hRadius

theorem gate_pass_requires_sign_input_written
    (g : RP3SpatialSliceCurvatureSignGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.curvatureSignInputWritten) :
    g.curvatureSignInputWritten := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaRP3SpatialSliceCurvatureSignGate
end JanusFormal
