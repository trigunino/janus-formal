import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NonlinearResidualFactorization

namespace JanusFormal
namespace P0EFTJanusZ4ObstructionWardIdentity

set_option autoImplicit false

structure ObstructionWardIdentity where
  obstructionDeclared : Prop
  z4CurrentDivergenceDeclared : Prop
  anomalyTermDeclared : Prop
  obstructionEqualsDivergenceMinusAnomaly : Prop
  determinantWeightCompatible : Prop
  anomalyCancellationDerived : Prop

def obstructionWardIdentityReady (w : ObstructionWardIdentity) : Prop :=
  w.obstructionDeclared /\
  w.z4CurrentDivergenceDeclared /\
  w.anomalyTermDeclared /\
  w.obstructionEqualsDivergenceMinusAnomaly /\
  w.determinantWeightCompatible

def obstructionWardClosureReady (w : ObstructionWardIdentity) : Prop :=
  obstructionWardIdentityReady w /\
  w.anomalyCancellationDerived

theorem ward_identity_tracks_anomaly_term
    (w : ObstructionWardIdentity)
    (h : obstructionWardIdentityReady w) :
    w.anomalyTermDeclared := by
  exact h.right.right.left

theorem ward_identity_does_not_cancel_anomaly
    (w : ObstructionWardIdentity)
    (_h : obstructionWardIdentityReady w)
    (hMissing : Not w.anomalyCancellationDerived) :
    Not (obstructionWardClosureReady w) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4ObstructionWardIdentity
end JanusFormal
