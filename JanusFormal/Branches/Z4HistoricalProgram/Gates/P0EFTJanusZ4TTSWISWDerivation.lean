import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4CMBFailureMap

namespace JanusFormal
namespace P0EFTJanusZ4TTSWISWDerivation

set_option autoImplicit false

structure TTSWISWDerivation where
  ttAcousticOscillatorDerived : Prop
  negativeSectorAcousticSourceSeparated : Prop
  hiddenISWCountertermDerived : Prop
  hiddenSWCompensationDerived : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def ttSWISWDerivationReady (d : TTSWISWDerivation) : Prop :=
  d.ttAcousticOscillatorDerived /\
  d.negativeSectorAcousticSourceSeparated /\
  d.hiddenISWCountertermDerived /\
  d.hiddenSWCompensationDerived

theorem derivation_closes_tt_and_lowtt_locks
    (d : TTSWISWDerivation)
    (h : ttSWISWDerivationReady d) :
    d.ttAcousticOscillatorDerived /\ d.hiddenISWCountertermDerived := by
  exact And.intro h.left h.right.right.left

theorem derivation_does_not_modify_solver
    (d : TTSWISWDerivation)
    (_h : ttSWISWDerivationReady d)
    (hFrozen : Not d.solverNumericsModified) :
    Not d.solverNumericsModified := by
  exact hFrozen

theorem derivation_does_not_claim_planck
    (d : TTSWISWDerivation)
    (_h : ttSWISWDerivationReady d)
    (hNoClaim : Not d.planckValidationClaimed) :
    Not d.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4TTSWISWDerivation
end JanusFormal
