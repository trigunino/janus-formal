import Mathlib

namespace JanusFormal

structure BianchiDustHypotheses where
  sameSectorConserved : Prop
  transportedContinuity : Prop
  transportedForceCancellation : Prop

structure BianchiDustClosure where
  rPlusZero : Prop
  rMinusZero : Prop

theorem conditionalDustClosure
    (h : BianchiDustHypotheses)
    (hSame : h.sameSectorConserved)
    (hContinuity : h.transportedContinuity)
    (hForce : h.transportedForceCancellation) :
    h.sameSectorConserved ∧ h.transportedContinuity ∧ h.transportedForceCancellation := by
  exact And.intro hSame (And.intro hContinuity hForce)

end JanusFormal
