import Mathlib

namespace JanusFormal
namespace P0EFTJanusWorldvolumeParityAnomaly

set_option autoImplicit false

/-- Twice the effective Abelian Chern--Simons level in an integer convention. -/
def doubledEffectiveLevel
    (bareLevel fermionMultiplicity : ℤ) : ℤ :=
  2 * bareLevel + fermionMultiplicity

/-- An exactly vanishing effective level with integral bare level requires an even fermion multiplicity. -/
theorem zero_effective_level_requires_even_fermion_multiplicity
    (bareLevel fermionMultiplicity : ℤ)
    (hZero : doubledEffectiveLevel bareLevel fermionMultiplicity = 0) :
    fermionMultiplicity % 2 = 0 := by
  unfold doubledEffectiveLevel at hZero
  omega

/-- An odd number of unit-charge fermions obstructs a parity-symmetric zero level. -/
theorem odd_fermion_multiplicity_obstructs_zero_effective_level
    (bareLevel fermionMultiplicity : ℤ)
    (hOdd : fermionMultiplicity % 2 = 1) :
    doubledEffectiveLevel bareLevel fermionMultiplicity ≠ 0 := by
  intro hZero
  have hEven :=
    zero_effective_level_requires_even_fermion_multiplicity
      bareLevel fermionMultiplicity hZero
  omega

/-- PT reverses a signed Chern--Simons level. -/
def ptLevel (level : ℤ) : ℤ := -level

@[simp] theorem pt_level_is_involutive (level : ℤ) :
    ptLevel (ptLevel level) = level := by
  simp [ptLevel]

/-- A nonzero level cannot itself be invariant under the PT sign reversal. -/
theorem nonzero_level_is_not_pt_fixed
    (level : ℤ)
    (hNonzero : level ≠ 0) :
    ptLevel level ≠ level := by
  intro hFixed
  apply hNonzero
  unfold ptLevel at hFixed
  omega

/--
A Janus-compatible quantum world-volume can preserve the paired PT theory even
when each individual fold carries opposite parity-anomalous levels.
-/
structure PairedParityAnomalyCancellation where
  positiveFoldLevel : ℤ
  negativeFoldLevel : ℤ
  foldPairingLaw : negativeFoldLevel = -positiveFoldLevel
  totalLevelCancels : positiveFoldLevel + negativeFoldLevel = 0

/-- The PT pairing law automatically cancels the total level. -/
theorem pt_pairing_cancels_total_level
    (positiveFoldLevel negativeFoldLevel : ℤ)
    (hPair : negativeFoldLevel = -positiveFoldLevel) :
    positiveFoldLevel + negativeFoldLevel = 0 := by
  rw [hPair]
  omega

/--
Parity anomaly fixes discrete data, but scale generation additionally requires
a stable RG or nonperturbative mechanism.  In three dimensions there is no
ordinary local bulk Weyl-anomaly coefficient that can be used as a free scale
selector; any proposed route must identify its actual anomaly, boundary, or
spontaneous-breaking mechanism explicitly.
-/
structure QuantumAnomalyScaleStatus where
  pairedParityAnomalyCancelled : Prop
  compactChernSimonsLevelQuantized : Prop
  matterContentFixed : Prop
  scaleGeneratingOperatorIdentified : Prop
  betaFunctionOrGapEquationComputed : Prop
  stableVacuumProved : Prop
  generatedScaleMappedToLLCharge : Prop


def anomalyScaleRouteClosed (s : QuantumAnomalyScaleStatus) : Prop :=
  s.pairedParityAnomalyCancelled /\
  s.compactChernSimonsLevelQuantized /\
  s.matterContentFixed /\
  s.scaleGeneratingOperatorIdentified /\
  s.betaFunctionOrGapEquationComputed /\
  s.stableVacuumProved /\
  s.generatedScaleMappedToLLCharge

end P0EFTJanusWorldvolumeParityAnomaly
end JanusFormal
