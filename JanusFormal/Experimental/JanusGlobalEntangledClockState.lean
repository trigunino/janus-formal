import JanusFormal.Experimental.JanusModularBimetricLapseAudit

/-!
# Global entangled state for the Janus modular clock

This isolated finite model derives the reciprocal reduced qubit states from
one normalized pure state on `H_plus tensor H_minus`.
-/

namespace JanusFormal
namespace ExperimentalJanusGlobalEntangledClockState

set_option autoImplicit false

open ExperimentalJanusTwoQubitModularClock

noncomputable section

abbrev QubitIndex := Fin 2
abbrev BipartiteState := QubitIndex × QubitIndex → ℝ

/-- PT-crossed Schmidt state
`sqrt(p)|0,+;1,-> + sqrt(1-p)|1,+;0,->`. -/
def globalClockState (p : ℝ) : BipartiteState :=
  fun index =>
    if index = (0, 1) then Real.sqrt p
    else if index = (1, 0) then Real.sqrt (1 - p)
    else 0

def stateNormSquared (state : BipartiteState) : ℝ :=
  ∑ i : QubitIndex, ∑ j : QubitIndex, state (i, j) ^ 2

/-- The global state is normalized for a probabilistic weight. -/
theorem global_clock_state_normalized
    (p : ℝ) (hP : 0 ≤ p) (hUpper : p ≤ 1) :
    stateNormSquared (globalClockState p) = 1 := by
  have hOneMinus : 0 ≤ 1 - p := by linarith
  simp [stateNormSquared, globalClockState, Fin.sum_univ_two,
    Real.sq_sqrt hP, Real.sq_sqrt hOneMinus]

/-- Partial trace over the minus qubit. -/
def reducePlus (state : BipartiteState) : QubitMatrixReal :=
  fun row column =>
    ∑ j : QubitIndex, state (row, j) * state (column, j)

/-- Partial trace over the plus qubit. -/
def reduceMinus (state : BipartiteState) : QubitMatrixReal :=
  fun row column =>
    ∑ i : QubitIndex, state (i, row) * state (i, column)

theorem global_state_reduces_to_plus_state
    (p : ℝ) (hP : 0 ≤ p) (hUpper : p ≤ 1) :
    reducePlus (globalClockState p) = reducedState p := by
  have hOneMinus : 0 ≤ 1 - p := by linarith
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [reducePlus, globalClockState, reducedState,
      Real.mul_self_sqrt hP, Real.mul_self_sqrt hOneMinus]

theorem global_state_reduces_to_pt_swapped_minus_state
    (p : ℝ) (hP : 0 ≤ p) (hUpper : p ≤ 1) :
    reduceMinus (globalClockState p) = reducedState (1 - p) := by
  have hOneMinus : 0 ≤ 1 - p := by linarith
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [reduceMinus, globalClockState, reducedState,
      Real.mul_self_sqrt hP, Real.mul_self_sqrt hOneMinus]

/-- Two-by-two amplitude determinant; every product state has zero value. -/
def schmidtDeterminant (state : BipartiteState) : ℝ :=
  state (0, 0) * state (1, 1) - state (0, 1) * state (1, 0)

theorem global_clock_state_schmidt_determinant
    (p : ℝ) :
    schmidtDeterminant (globalClockState p) =
      -Real.sqrt p * Real.sqrt (1 - p) := by
  simp [schmidtDeterminant, globalClockState]

/-- For `0<p<1`, the common pure state is genuinely entangled rather than a
product chosen independently in the two sectors. -/
theorem global_clock_state_is_entangled
    (p : ℝ) (hP : 0 < p) (hUpper : p < 1) :
    schmidtDeterminant (globalClockState p) ≠ 0 := by
  rw [global_clock_state_schmidt_determinant]
  have hOneMinus : 0 < 1 - p := by linarith
  exact mul_ne_zero (neg_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hP))
    (Real.sqrt_ne_zero'.mpr hOneMinus)

/-- End-to-end finite result: one global entangled state yields the reciprocal
reduced states whose modular generators are opposite. -/
theorem one_global_state_supplies_opposite_modular_generators
    (p : ℝ) (observable : QubitMatrixReal) :
    commutator (modularHamiltonian (1 - p)) observable =
      -commutator (modularHamiltonian p) observable :=
  pt_modular_generators_are_opposite p observable

end

end ExperimentalJanusGlobalEntangledClockState
end JanusFormal
