import JanusFormal.P0EFTJanusProjectiveTunnelInterface

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSignedCoverTimeParityGate

set_option autoImplicit false

structure SignedCoverTimeParityGate where
  activeCoreZ2Sigma : Prop
  signedTimeCoordinateOnS4CoverDefined : Prop
  z2EquivariantTimeCoordinateDerived : Prop
  antipodalPullbackPlusOrMinusSelf : Prop
  flrwTimeGaugeUsesSignedCoordinate : Prop
  observationalTimeGaugeFitForbidden : Prop
  usesCompressedPlanckLCDMBackground : Prop
  usesArchivedZ4Background : Prop
  signedCoverTimeParityInputWritten : Prop
  gatePassed : Prop

def signedCoverTimeParityPolicyClosed
    (g : SignedCoverTimeParityGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.signedTimeCoordinateOnS4CoverDefined /\
  g.z2EquivariantTimeCoordinateDerived /\
  g.antipodalPullbackPlusOrMinusSelf /\
  g.flrwTimeGaugeUsesSignedCoordinate /\
  g.observationalTimeGaugeFitForbidden /\
  Not g.usesCompressedPlanckLCDMBackground /\
  Not g.usesArchivedZ4Background

theorem gate_pass_requires_written_time_parity_input
    (g : SignedCoverTimeParityGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.signedCoverTimeParityInputWritten) :
    g.signedCoverTimeParityInputWritten := by
  exact hImplies _hGate

theorem policy_forbids_archived_z4_and_planck_background
    (g : SignedCoverTimeParityGate)
    (h : signedCoverTimeParityPolicyClosed g) :
    Not g.usesCompressedPlanckLCDMBackground /\ Not g.usesArchivedZ4Background := by
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end P0EFTJanusZ2SigmaSignedCoverTimeParityGate
end JanusFormal
