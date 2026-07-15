import JanusFormal.Experimental.JanusRelationalEntropyClock

/-!
# Common relational clock bridge

This isolated module distinguishes one shared event parameter from the two
sector proper times and their lapse rates.
-/

namespace JanusFormal
namespace ExperimentalJanusCommonRelationalClockBridge

set_option autoImplicit false

/-- Plus-sector proper time read against a common clock. -/
def plusProperTime (plusLapse commonClock : ℝ) : ℝ :=
  plusLapse * commonClock

/-- PT-opposite minus-sector proper time read against the same common clock. -/
def minusProperTime (minusLapse commonClock : ℝ) : ℝ :=
  -minusLapse * commonClock

/-- A common parameter is compatible with distinct positive lapse rates. -/
theorem common_clock_does_not_force_equal_lapses
    (plusLapse minusLapse : ℝ)
    (hDistinct : plusLapse ≠ minusLapse) :
    plusProperTime plusLapse 1 ≠ plusProperTime minusLapse 1 := by
  simpa [plusProperTime]

/-- A monotone relational clock induces increasing plus proper time. -/
theorem common_clock_orders_plus_sector
    (clock : ℝ → ℝ)
    (plusLapse : ℝ)
    (hClock : StrictMono clock)
    (hLapse : 0 < plusLapse) :
    StrictMono (fun parameter => plusProperTime plusLapse (clock parameter)) := by
  intro first second hOrder
  unfold plusProperTime
  exact mul_lt_mul_of_pos_left (hClock hOrder) hLapse

/-- The same monotone clock induces the opposite PT orientation in the minus
proper time without reversing the common ordering of events. -/
theorem common_clock_supports_opposite_pt_arrow
    (clock : ℝ → ℝ)
    (minusLapse : ℝ)
    (hClock : StrictMono clock)
    (hLapse : 0 < minusLapse) :
    StrictAnti (fun parameter => minusProperTime minusLapse (clock parameter)) := by
  intro first second hOrder
  unfold minusProperTime
  have hClockOrder := hClock hOrder
  nlinarith

/-- Equal unit lapse in both metric ansatzes is an additional synchronization
condition, not a consequence of merely naming one common parameter. -/
def UnitLapseSynchronization (plusLapse minusLapse : ℝ) : Prop :=
  plusLapse = 1 ∧ minusLapse = 1

theorem unit_lapse_synchronization_fixes_ratio
    (plusLapse minusLapse : ℝ)
    (hSync : UnitLapseSynchronization plusLapse minusLapse) :
    minusLapse / plusLapse = 1 := by
  rcases hSync with ⟨rfl, rfl⟩
  norm_num

end ExperimentalJanusCommonRelationalClockBridge
end JanusFormal
