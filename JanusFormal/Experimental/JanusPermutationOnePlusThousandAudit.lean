import Mathlib

namespace JanusFormal
namespace JanusPermutationOnePlusThousandAudit

set_option autoImplicit false

noncomputable section

abbrev State1001 := Fin 1001 → ℝ

def mean1001 (x : State1001) : ℝ :=
  (∑ i, x i) / 1001

def collectivePart (x : State1001) : State1001 :=
  fun _ => mean1001 x

def relativePart (x : State1001) : State1001 :=
  fun i => x i - mean1001 x

/-- Every 1001-component state splits explicitly into one uniform component
and a relative component. -/
theorem collective_add_relative (x : State1001) :
    collectivePart x + relativePart x = x := by
  funext i
  simp [collectivePart, relativePart]

/-- The relative component has zero total amplitude. -/
theorem relativePart_sum_zero (x : State1001) :
    ∑ i, relativePart x i = 0 := by
  simp [relativePart, mean1001, Finset.sum_sub_distrib]
  ring

/-- A common scalar evolution preserves the uniform collective sector. -/
theorem common_evolution_preserves_collective
    (rate : ℝ) (x : State1001) :
    rate • collectivePart x = collectivePart (rate • x) := by
  funext i
  simp [collectivePart, mean1001]
  rw [← Finset.mul_sum]
  ring

/-- The same common evolution preserves the zero-sum relative sector. -/
theorem common_evolution_preserves_relative
    (rate : ℝ) (x : State1001) :
    rate • relativePart x = relativePart (rate • x) := by
  funext i
  simp [relativePart, mean1001]
  rw [← Finset.mul_sum]
  ring

def basisState (i : Fin 1001) : State1001 :=
  fun j => if j = i then 1 else 0

/-- A scalar Hamiltonian assigns the same eigenvalue to every basis state;
it therefore cannot order the 1000 relative directions. -/
theorem scalar_hamiltonian_is_degenerate
    (energy : ℝ) (i j : Fin 1001) :
    (energy • basisState i) i =
      (energy • basisState j) j := by
  simp [basisState]

end
end JanusPermutationOnePlusThousandAudit
end JanusFormal
