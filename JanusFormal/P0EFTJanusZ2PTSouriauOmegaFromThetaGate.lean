namespace JanusFormal
namespace P0EFTJanusZ2PTSouriauOmegaFromThetaGate

set_option autoImplicit false

structure PTSouriauOmegaFromThetaGate where
  thetaPTReady : Prop
  thetaPTTrivial : Prop
  omegaEqualsDeltaTheta : Prop
  claimsNonzeroPeriods : Prop

def omegaThetaRouteOpen (g : PTSouriauOmegaFromThetaGate) : Prop :=
  g.thetaPTReady /\ Not g.thetaPTTrivial /\ g.omegaEqualsDeltaTheta

theorem trivial_theta_blocks_nonzero_periods
    (g : PTSouriauOmegaFromThetaGate)
    (_hReady : g.thetaPTReady)
    (hTrivial : g.thetaPTTrivial)
    (_hOmega : g.omegaEqualsDeltaTheta) :
    Not (omegaThetaRouteOpen g) := by
  intro h
  exact h.right.left hTrivial

theorem trivial_theta_blocks_period_claim
    (g : PTSouriauOmegaFromThetaGate)
    (hTrivialImpliesNoPeriods : g.thetaPTTrivial -> Not g.claimsNonzeroPeriods)
    (hTrivial : g.thetaPTTrivial) :
    Not g.claimsNonzeroPeriods :=
  hTrivialImpliesNoPeriods hTrivial

end P0EFTJanusZ2PTSouriauOmegaFromThetaGate
end JanusFormal
