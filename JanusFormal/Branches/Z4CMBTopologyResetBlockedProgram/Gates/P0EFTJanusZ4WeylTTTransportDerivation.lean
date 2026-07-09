import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TTSWISWPlanckGate

namespace JanusFormal
namespace P0EFTJanusZ4WeylTTTransportDerivation

set_option autoImplicit false

structure WeylTTTransportDerivation where
  mirrorEvenWeylSourceDerived : Prop
  determinantLeakageRemoved : Prop
  crossSectorLeakageRemoved : Prop
  ttClockWardCountertermDerived : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def derivationReady (d : WeylTTTransportDerivation) : Prop :=
  d.mirrorEvenWeylSourceDerived /\
  d.determinantLeakageRemoved /\
  d.crossSectorLeakageRemoved /\
  d.ttClockWardCountertermDerived

theorem derivation_closes_weyl_and_clock_guards
    (d : WeylTTTransportDerivation)
    (h : derivationReady d) :
    d.mirrorEvenWeylSourceDerived /\ d.ttClockWardCountertermDerived := by
  exact And.intro h.left h.right.right.right

theorem derivation_does_not_claim_planck
    (d : WeylTTTransportDerivation)
    (_h : derivationReady d)
    (hNoClaim : Not d.planckValidationClaimed) :
    Not d.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4WeylTTTransportDerivation
end JanusFormal
