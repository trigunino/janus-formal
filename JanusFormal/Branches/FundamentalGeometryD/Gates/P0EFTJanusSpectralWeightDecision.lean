import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpectralWeightDecision

set_option autoImplicit false

/-- Competing unweighted and degeneracy-weighted first-mode laws. -/
structure CompetingSpectralLocks where
  circleModulus : ℝ
  piConstant : ℝ
  piConstantPositive : 0 < piConstant
  unweightedIsotropy :
    circleModulus ^ 2 = 2 * piConstant ^ 2
  scalarDegeneracyBalance :
    3 * circleModulus ^ 2 = 4 * piConstant ^ 2

/-- The unweighted and `3:2` degeneracy-weighted locks are incompatible. -/
theorem unweighted_and_scalar_degeneracy_locks_incompatible
    (s : CompetingSpectralLocks) : False := by
  have hPiSquare : 0 < s.piConstant ^ 2 :=
    pow_pos s.piConstantPositive 2
  nlinarith [s.unweightedIsotropy, s.scalarDegeneracyBalance]

/-- No positive-pi datum can satisfy both candidate laws. -/
theorem no_competing_spectral_lock_data :
    ¬ ∃ s : CompetingSpectralLocks, True := by
  rintro ⟨s, _⟩
  exact unweighted_and_scalar_degeneracy_locks_incompatible s

/--
The decision rule is therefore explicit: equal-mode isotropy survives only if
the renormalized determinant produces equal effective weights.  If the actual
weights reduce to the first scalar degeneracies `3:2`, the unweighted branch is
rejected and the weighted branch is selected.
-/
structure SpectralBranchDecisionStatus where
  fullFieldContentDerived : Prop
  gaugeAndGhostContributionsIncluded : Prop
  fermionSignsIncluded : Prop
  regularizedWeightsComputed : Prop
  effectiveWeightsEqual : Prop
  effectiveWeightsThreeToTwo : Prop
  unweightedBranchAcceptedOrRejected : Prop
  weightedBranchAcceptedOrRejected : Prop


def spectralBranchDecisionClosed
    (s : SpectralBranchDecisionStatus) : Prop :=
  s.fullFieldContentDerived /\
  s.gaugeAndGhostContributionsIncluded /\
  s.fermionSignsIncluded /\
  s.regularizedWeightsComputed /\
  s.unweightedBranchAcceptedOrRejected /\
  s.weightedBranchAcceptedOrRejected /\
  Not (s.effectiveWeightsEqual /\ s.effectiveWeightsThreeToTwo)

end P0EFTJanusSpectralWeightDecision
end JanusFormal
