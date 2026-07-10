import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPositiveKineticMassEigenmodes
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusReducedHamiltonianStability

set_option autoImplicit false

open P0EFTJanusPositiveKineticMassEigenmodes
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Reduced positive-kinetic Hamiltonian on the proportional branch. -/
def reducedHamiltonian
    (planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus : ℝ) : ℝ :=
  safeQuadraticEnergy planckSquared relativeMassSquared hPlus hMinus +
    proportionalInteractionEnergy beta1 beta2 c

/-- Every term of the reduced Hamiltonian is nonnegative in the safe cone. -/
theorem reduced_hamiltonian_nonnegative
    (planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus : ℝ)
    (hPlanck : 0 < planckSquared)
    (hMass : 0 ≤ relativeMassSquared)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hC : 0 < c) :
    0 ≤ reducedHamiltonian
      planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus := by
  unfold reducedHamiltonian safeQuadraticEnergy
  have hKinetic :
      0 ≤ planckSquared * (hPlus ^ 2 + hMinus ^ 2) :=
    mul_nonneg (le_of_lt hPlanck)
      (add_nonneg (sq_nonneg hPlus) (sq_nonneg hMinus))
  have hRelative :
      0 ≤ relativeMassSquared * relativeMode hPlus hMinus ^ 2 :=
    mul_nonneg hMass (sq_nonneg _)
  have hInteraction :
      0 ≤ proportionalInteractionEnergy beta1 beta2 c := by
    rw [interaction_energy_factorization]
    exact mul_nonneg (sq_nonneg _)
      (le_of_lt (relative_shape_positive beta1 beta2 c hBeta1 hBeta2 hC))
  positivity

/-- Nonzero spin-2 fluctuations give strictly positive reduced energy. -/
theorem reduced_hamiltonian_positive_for_nonzero_modes
    (planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus : ℝ)
    (hPlanck : 0 < planckSquared)
    (hMass : 0 ≤ relativeMassSquared)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hC : 0 < c)
    (hMode : hPlus ≠ 0 ∨ hMinus ≠ 0) :
    0 < reducedHamiltonian
      planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus := by
  unfold reducedHamiltonian
  have hQuadratic := safe_quadratic_energy_positive
    planckSquared relativeMassSquared hPlus hMinus hPlanck hMass hMode
  have hInteraction :
      0 ≤ proportionalInteractionEnergy beta1 beta2 c := by
    rw [interaction_energy_factorization]
    exact mul_nonneg (sq_nonneg _)
      (le_of_lt (relative_shape_positive beta1 beta2 c hBeta1 hBeta2 hC))
  exact add_pos_of_pos_of_nonneg hQuadratic hInteraction

/-- A displaced proportional ratio gives strictly positive energy even at zero fluctuation. -/
theorem reduced_hamiltonian_positive_away_from_pt_ratio
    (planckSquared relativeMassSquared beta1 beta2 c : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hC : 0 < c)
    (hNotOne : c ≠ 1) :
    0 < reducedHamiltonian
      planckSquared relativeMassSquared beta1 beta2 c 0 0 := by
  unfold reducedHamiltonian safeQuadraticEnergy
  simp [relativeMode]
  exact interaction_energy_positive_away_from_symmetric_point
    beta1 beta2 c hBeta1 hBeta2 hC hNotOne

/-- The symmetric zero-fluctuation configuration has zero reduced energy. -/
theorem reduced_hamiltonian_at_pt_vacuum
    (planckSquared relativeMassSquared beta1 beta2 : ℝ) :
    reducedHamiltonian
      planckSquared relativeMassSquared beta1 beta2 1 0 0 = 0 := by
  unfold reducedHamiltonian safeQuadraticEnergy
  simp [relativeMode, interaction_energy_at_symmetric_point]

/--
The reduced branch has one global nonnegative vacuum in the positive
proportional sector. Extending this result to the full field theory requires the
Hassan--Rosen constraint, boundary terms and nonlinear matter stability.
-/
structure ReducedHamiltonianClosureStatus where
  positiveKineticConeDerived : Prop
  relativeMassNonnegative : Prop
  ptPotentialConeDerived : Prop
  proportionalVacuumUnique : Prop
  reducedHamiltonianBoundedBelow : Prop
  fullConstraintReductionDerived : Prop
  nonlinearMatterHamiltonianPositive : Prop
  boundaryHamiltonianIncluded : Prop
  fullPhysicalHamiltonianBoundedBelow : Prop


def reducedHamiltonianClosure
    (s : ReducedHamiltonianClosureStatus) : Prop :=
  s.positiveKineticConeDerived /\
  s.relativeMassNonnegative /\
  s.ptPotentialConeDerived /\
  s.proportionalVacuumUnique /\
  s.reducedHamiltonianBoundedBelow /\
  s.fullConstraintReductionDerived /\
  s.nonlinearMatterHamiltonianPositive /\
  s.boundaryHamiltonianIncluded /\
  s.fullPhysicalHamiltonianBoundedBelow

end P0EFTJanusReducedHamiltonianStability
end JanusFormal
