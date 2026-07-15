import JanusFormal.Experimental.JanusCommonRelationalClockBridge

/-!
# Two-qubit modular clock candidate

This isolated finite model tests whether a PT-related pair of faithful reduced
states can generate one modular parameter with opposite sector orientations.
-/

namespace JanusFormal
namespace ExperimentalJanusTwoQubitModularClock

set_option autoImplicit false

noncomputable section

abbrev QubitMatrixReal := Matrix (Fin 2) (Fin 2) ℝ

/-- Diagonal reduced qubit state with weights `(p, 1-p)`. -/
def reducedState (p : ℝ) : QubitMatrixReal :=
  !![p, 0; 0, 1 - p]

theorem reduced_state_trace_one (p : ℝ) :
    Matrix.trace (reducedState p) = 1 := by
  simp [reducedState, Matrix.trace, Fin.sum_univ_two]

/-- Faithfulness condition for the finite reduced state. -/
def FaithfulWeight (p : ℝ) : Prop :=
  0 < p ∧ p < 1

theorem pt_swapped_weight_faithful
    (p : ℝ)
    (hFaithful : FaithfulWeight p) :
    FaithfulWeight (1 - p) := by
  unfold FaithfulWeight at hFaithful ⊢
  constructor <;> linarith

/-- Finite modular Hamiltonian `K = -log rho` for the diagonal state. -/
def modularHamiltonian (p : ℝ) : QubitMatrixReal :=
  !![-Real.log p, 0; 0, -Real.log (1 - p)]

def scalarMatrix (value : ℝ) : QubitMatrixReal :=
  !![value, 0; 0, value]

/-- PT swapping the two weights sends the modular Hamiltonian to its negative
up to a central scalar. -/
theorem pt_modular_hamiltonians_sum_to_central
    (p : ℝ) :
    modularHamiltonian p + modularHamiltonian (1 - p) =
      scalarMatrix (-Real.log p - Real.log (1 - p)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularHamiltonian, scalarMatrix] <;> ring

def commutator (first second : QubitMatrixReal) : QubitMatrixReal :=
  first * second - second * first

/-- Central shifts do not affect modular evolution, so the two PT-related
reduced states generate exactly opposite commutator flows. -/
theorem pt_modular_generators_are_opposite
    (p : ℝ) (observable : QubitMatrixReal) :
    commutator (modularHamiltonian (1 - p)) observable =
      -commutator (modularHamiltonian p) observable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, modularHamiltonian, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

/-- Spectral gap controlling the nontrivial two-level modular rate. -/
def modularGap (p : ℝ) : ℝ :=
  Real.log ((1 - p) / p)

theorem pt_modular_gap_reverses
    (p : ℝ)
    (hP : p ≠ 0)
    (hOneMinusP : 1 - p ≠ 0) :
    modularGap (1 - p) = -modularGap p := by
  unfold modularGap
  have hRatio : p / (1 - p) = ((1 - p) / p)⁻¹ := by
    field_simp [hP, hOneMinusP]
  have hCancel : 1 - (1 - p) = p := by ring
  rw [hCancel, hRatio, Real.log_inv]

/-- Exact PT reciprocity predicts equal modular-rate magnitudes, hence a unit
relative rate whenever the modular flow is nontrivial. -/
theorem pt_modular_rate_ratio_is_one
    (p : ℝ)
    (hP : p ≠ 0)
    (hOneMinusP : 1 - p ≠ 0)
    (hGap : modularGap p ≠ 0) :
    |modularGap (1 - p)| / |modularGap p| = 1 := by
  rw [pt_modular_gap_reverses p hP hOneMinusP, abs_neg]
  exact div_self (abs_ne_zero.mpr hGap)

/-- The maximally mixed state has no nontrivial modular clock. -/
theorem maximally_mixed_modular_clock_stalls :
    modularGap ((1 : ℝ) / 2) = 0 := by
  norm_num [modularGap]

end

end ExperimentalJanusTwoQubitModularClock
end JanusFormal
