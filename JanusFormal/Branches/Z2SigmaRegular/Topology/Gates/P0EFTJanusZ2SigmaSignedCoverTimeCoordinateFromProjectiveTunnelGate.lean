import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusZ2SigmaSignedCoverTimeParityGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSignedCoverTimeCoordinateFromProjectiveTunnelGate

set_option autoImplicit false

structure SignedCoverTimeCoordinateFromProjectiveTunnelGate where
  activeCoreZ2Sigma : Prop
  projectiveTunnelClosed : Prop
  s4CoverDefined : Prop
  antipodalDeckTransformationDefined : Prop
  bigBangPoleDefined : Prop
  bigCrunchPoleDefined : Prop
  polesAntipodal : Prop
  signedHeightAlongPoleAxisDefined : Prop
  antipodalPullbackMinusSelf : Prop
  observationalTimeGaugeFitForbidden : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  signedCoverTimeCoordinateWritten : Prop
  gatePassed : Prop

def signedCoverTimeCoordinatePolicyClosed
    (g : SignedCoverTimeCoordinateFromProjectiveTunnelGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.projectiveTunnelClosed /\
  g.s4CoverDefined /\
  g.antipodalDeckTransformationDefined /\
  g.bigBangPoleDefined /\
  g.bigCrunchPoleDefined /\
  g.polesAntipodal /\
  g.signedHeightAlongPoleAxisDefined /\
  g.antipodalPullbackMinusSelf /\
  g.observationalTimeGaugeFitForbidden /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background

theorem antipodal_pole_axis_supplies_odd_signed_cover_time
    (g : SignedCoverTimeCoordinateFromProjectiveTunnelGate)
    (h : signedCoverTimeCoordinatePolicyClosed g) :
    g.antipodalPullbackMinusSelf := by
  exact h.2.2.2.2.2.2.2.2.1

theorem gate_pass_requires_signed_time_coordinate_manifest
    (g : SignedCoverTimeCoordinateFromProjectiveTunnelGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.signedCoverTimeCoordinateWritten) :
    g.signedCoverTimeCoordinateWritten := by
  exact hImplies _hGate

end P0EFTJanusZ2SigmaSignedCoverTimeCoordinateFromProjectiveTunnelGate
end JanusFormal
