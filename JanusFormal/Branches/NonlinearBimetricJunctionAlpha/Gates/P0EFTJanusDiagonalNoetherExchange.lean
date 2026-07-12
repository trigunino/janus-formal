import Mathlib

namespace JanusFormal
namespace P0EFTJanusDiagonalNoetherExchange

set_option autoImplicit false

/-- Reduced divergence data for a common diffeomorphism-invariant interaction. -/
structure ExchangeDivergence where
  plusWeightedDivergence : ℝ
  minusWeightedDivergence : ℝ
  diagonalNoetherIdentity :
    plusWeightedDivergence + minusWeightedDivergence = 0

/-- Conservation in one sector is equivalent to conservation in the other. -/
theorem plus_conserved_iff_minus_conserved
    (d : ExchangeDivergence) :
    d.plusWeightedDivergence = 0 <->
      d.minusWeightedDivergence = 0 := by
  constructor <;> intro h
  · linarith [d.diagonalNoetherIdentity]
  · linarith [d.diagonalNoetherIdentity]

/-- A nonzero exchange current forbids imposing separate conservation on both sides. -/
theorem nonzero_exchange_forbids_separate_conservation
    (d : ExchangeDivergence)
    (hExchange : d.plusWeightedDivergence ≠ 0) :
    Not (d.plusWeightedDivergence = 0 /\
      d.minusWeightedDivergence = 0) := by
  intro h
  exact hExchange h.1

/-- The exchange divergences are opposite. -/
theorem exchange_divergences_are_opposite
    (d : ExchangeDivergence) :
    d.minusWeightedDivergence = -d.plusWeightedDivergence := by
  linarith [d.diagonalNoetherIdentity]

/--
A complete nonlinear model must derive the weighted exchange identity from one
action.  Separate vanishing of the two interaction divergences is a special
zero-exchange branch, not the generic consequence of diagonal diffeomorphism
invariance.
-/
structure DiagonalNoetherClosureStatus where
  commonDiffeomorphismActionDefined : Prop
  metricVariationsTracked : Prop
  matterVariationsTracked : Prop
  determinantWeightsTracked : Prop
  combinedNoetherIdentityDerived : Prop
  exchangeCurrentIdentified : Prop
  zeroExchangeBranchJustifiedIfUsed : Prop
  bianchiCompatibilityProved : Prop


def diagonalNoetherClosure
    (s : DiagonalNoetherClosureStatus) : Prop :=
  s.commonDiffeomorphismActionDefined /\
  s.metricVariationsTracked /\
  s.matterVariationsTracked /\
  s.determinantWeightsTracked /\
  s.combinedNoetherIdentityDerived /\
  s.exchangeCurrentIdentified /\
  s.zeroExchangeBranchJustifiedIfUsed /\
  s.bianchiCompatibilityProved

end P0EFTJanusDiagonalNoetherExchange
end JanusFormal
