import Mathlib

namespace JanusFormal
namespace JanusPModewiseHamiltonianSplit

set_option autoImplicit false

noncomputable section

/-- Common and relative coordinates of one arbitrary two-sheet field mode. -/
def commonMode (plus minus : ℝ) : ℝ := (plus + minus) / 2

def relativeMode (plus minus : ℝ) : ℝ := (plus - minus) / 2

/-- Equal-kinetic two-sheet quadratic Hamiltonian, with no assumed mode count. -/
def modeHamiltonian
    (kinetic relativeMass plus minus : ℝ) : ℝ :=
  (1 / 2) *
    (kinetic * plus ^ 2 + kinetic * minus ^ 2 +
      relativeMass * (plus - minus) ^ 2)

/-- P's quadratic structure diagonalizes canonically into one common and one
relative channel for every supplied field mode. -/
theorem modeHamiltonian_common_relative_split
    (kinetic relativeMass plus minus : ℝ) :
    modeHamiltonian kinetic relativeMass plus minus =
      kinetic * commonMode plus minus ^ 2 +
        (kinetic + 2 * relativeMass) * relativeMode plus minus ^ 2 := by
  simp [modeHamiltonian, commonMode, relativeMode]
  ring

/-- The common channel is massless with respect to the interaction term. -/
theorem diagonal_mode_has_no_relative_mass
    (kinetic relativeMass amplitude : ℝ) :
    modeHamiltonian kinetic relativeMass amplitude amplitude =
      kinetic * amplitude ^ 2 := by
  simp [modeHamiltonian]
  ring

/-- The relative channel receives the interaction mass shift. -/
theorem relative_mode_receives_mass_shift
    (kinetic relativeMass amplitude : ℝ) :
    modeHamiltonian kinetic relativeMass amplitude (-amplitude) =
      (kinetic + 2 * relativeMass) * amplitude ^ 2 := by
  simp [modeHamiltonian]
  ring

/-- The split is modewise for an arbitrary index type; P's two-sheet
Hamiltonian structure therefore does not select a finite number of modes. -/
theorem arbitrary_mode_family_split
    {ι : Type*} (kinetic relativeMass : ℝ)
    (plus minus : ι → ℝ) (i : ι) :
    modeHamiltonian kinetic relativeMass (plus i) (minus i) =
      kinetic * commonMode (plus i) (minus i) ^ 2 +
        (kinetic + 2 * relativeMass) *
          relativeMode (plus i) (minus i) ^ 2 :=
  modeHamiltonian_common_relative_split _ _ _ _

end
end JanusPModewiseHamiltonianSplit
end JanusFormal
