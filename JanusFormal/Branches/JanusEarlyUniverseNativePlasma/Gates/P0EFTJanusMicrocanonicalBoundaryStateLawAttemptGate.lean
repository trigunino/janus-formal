import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusBoundaryMicrostateIsotropicAverageCandidateGate

namespace JanusFormal
namespace P0EFTJanusMicrocanonicalBoundaryStateLawAttemptGate

set_option autoImplicit false

structure MicrocanonicalBoundaryStateLawAttemptGate where
  RhoBoundaryIsIdentityOver1001 : Prop
  SO3InvariantBoundaryState : Prop
  HiddenMicrostateCountEquals1001 : Prop
  EntropyRulerMapDerived : Prop
  PhotonBaryonRulerCouplingDerived : Prop

def MicrocanonicalBoundaryStateClosed
    (g : MicrocanonicalBoundaryStateLawAttemptGate) : Prop :=
  g.RhoBoundaryIsIdentityOver1001 /\
  g.SO3InvariantBoundaryState /\
  g.HiddenMicrostateCountEquals1001 /\
  g.EntropyRulerMapDerived /\
  g.PhotonBaryonRulerCouplingDerived

def MicrocanonicalBoundaryStateFrontier
    (g : MicrocanonicalBoundaryStateLawAttemptGate) : Prop :=
  g.RhoBoundaryIsIdentityOver1001 /\
  g.SO3InvariantBoundaryState /\
  g.HiddenMicrostateCountEquals1001 /\
  Not g.EntropyRulerMapDerived /\
  Not g.PhotonBaryonRulerCouplingDerived

theorem microcanonical_isotropy_still_needs_ruler_map
    (g : MicrocanonicalBoundaryStateLawAttemptGate)
    (hFrontier : MicrocanonicalBoundaryStateFrontier g) :
    Not (MicrocanonicalBoundaryStateClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusMicrocanonicalBoundaryStateLawAttemptGate
end JanusFormal
