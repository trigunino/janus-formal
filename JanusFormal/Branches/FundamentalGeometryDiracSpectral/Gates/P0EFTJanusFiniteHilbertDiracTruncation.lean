import Mathlib
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusGlobalSeparatedDiracModel

namespace JanusFormal
namespace P0EFTJanusFiniteHilbertDiracTruncation

set_option autoImplicit false

/-- Finite spectral truncation of a real diagonal Dirac operator. -/
structure FiniteDiracTruncation (rank : ℕ) where
  eigenvalue : Fin rank → ℝ

abbrev FiniteModeVector (rank : ℕ) := Fin rank → ℝ

/-- Euclidean pairing on one finite mode truncation. -/
def finitePairing {rank : ℕ}
    (first second : FiniteModeVector rank) : ℝ :=
  ∑ index, first index * second index

/-- Diagonal Dirac action in its separated eigenbasis. -/
def diagonalDirac {rank : ℕ} (operator : FiniteDiracTruncation rank)
    (vector : FiniteModeVector rank) : FiniteModeVector rank :=
  fun index => operator.eigenvalue index * vector index

/-- Every real diagonal truncation is symmetric for the Euclidean pairing. -/
theorem diagonal_dirac_symmetric {rank : ℕ}
    (operator : FiniteDiracTruncation rank)
    (first second : FiniteModeVector rank) :
    finitePairing (diagonalDirac operator first) second =
      finitePairing first (diagonalDirac operator second) := by
  apply Finset.sum_congr rfl
  intro index _
  simp [diagonalDirac]
  ring

/-- Shifted diagonal operator `D-z`. -/
def shiftedDirac {rank : ℕ} (operator : FiniteDiracTruncation rank)
    (shift : ℝ) (vector : FiniteModeVector rank) : FiniteModeVector rank :=
  fun index => (operator.eigenvalue index - shift) * vector index

/-- Explicit diagonal resolvent candidate. -/
noncomputable def diagonalResolvent {rank : ℕ} (operator : FiniteDiracTruncation rank)
    (shift : ℝ) (vector : FiniteModeVector rank) : FiniteModeVector rank :=
  fun index => vector index / (operator.eigenvalue index - shift)

theorem shifted_dirac_resolvent_left_inverse {rank : ℕ}
    (operator : FiniteDiracTruncation rank) (shift : ℝ)
    (hResolvent : ∀ index, operator.eigenvalue index ≠ shift)
    (vector : FiniteModeVector rank) :
    shiftedDirac operator shift (diagonalResolvent operator shift vector) =
      vector := by
  funext index
  unfold shiftedDirac diagonalResolvent
  field_simp [sub_ne_zero.mpr (hResolvent index)]

theorem shifted_dirac_resolvent_right_inverse {rank : ℕ}
    (operator : FiniteDiracTruncation rank) (shift : ℝ)
    (hResolvent : ∀ index, operator.eigenvalue index ≠ shift)
    (vector : FiniteModeVector rank) :
    diagonalResolvent operator shift (shiftedDirac operator shift vector) =
      vector := by
  funext index
  unfold shiftedDirac diagonalResolvent
  field_simp [sub_ne_zero.mpr (hResolvent index)]

/-- Squared diagonal operator is nonnegative in quadratic form. -/
theorem diagonal_square_nonnegative {rank : ℕ}
    (operator : FiniteDiracTruncation rank)
    (vector : FiniteModeVector rank) :
    0 ≤ finitePairing (diagonalDirac operator vector)
      (diagonalDirac operator vector) := by
  unfold finitePairing
  apply Finset.sum_nonneg
  intro index _
  exact mul_self_nonneg _

/-- Precise completion frontier from finite truncations to the global `ℓ²` operator. -/
structure HilbertLimitStatus where
  countableModeEnumerationConstructed : Prop
  finiteTruncationsExhaustModes : Prop
  l2CompletionConstructed : Prop
  weightedDenseDomainConstructed : Prop
  finiteOperatorsConvergeOnCore : Prop
  closureSelfAdjointProved : Prop
  resolventsConvergeInOperatorNorm : Prop
  limitingResolventCompact : Prop
  spectrumExhaustionProved : Prop

def hilbertLimitClosed (s : HilbertLimitStatus) : Prop :=
  s.countableModeEnumerationConstructed ∧ s.finiteTruncationsExhaustModes ∧
  s.l2CompletionConstructed ∧ s.weightedDenseDomainConstructed ∧
  s.finiteOperatorsConvergeOnCore ∧ s.closureSelfAdjointProved ∧
  s.resolventsConvergeInOperatorNorm ∧ s.limitingResolventCompact ∧
  s.spectrumExhaustionProved

end P0EFTJanusFiniteHilbertDiracTruncation
end JanusFormal
