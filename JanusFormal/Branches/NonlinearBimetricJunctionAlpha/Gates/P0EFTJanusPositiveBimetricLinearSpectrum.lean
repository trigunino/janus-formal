import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusPositiveBimetricLinearSpectrum

set_option autoImplicit false

open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Quadratic relative-mode potential around the proportional branch. -/
def relativeModePotential
    (massSquared hPlus hMinus : ℝ) : ℝ :=
  massSquared * (hPlus - hMinus) ^ 2

/-- The relative potential is nonnegative for a nonnegative mass coefficient. -/
theorem relative_mode_potential_nonnegative
    (massSquared hPlus hMinus : ℝ)
    (hMass : 0 ≤ massSquared) :
    0 ≤ relativeModePotential massSquared hPlus hMinus := by
  unfold relativeModePotential
  exact mul_nonneg hMass (sq_nonneg (hPlus - hMinus))

/-- With positive mass coefficient, the only zero is the diagonal mode. -/
theorem relative_mode_kernel_is_diagonal
    (massSquared hPlus hMinus : ℝ)
    (hMass : 0 < massSquared)
    (hZero : relativeModePotential massSquared hPlus hMinus = 0) :
    hPlus = hMinus := by
  unfold relativeModePotential at hZero
  have hMassNonzero : massSquared ≠ 0 := ne_of_gt hMass
  have hSquare : (hPlus - hMinus) ^ 2 = 0 :=
    (mul_eq_zero.mp hZero).resolve_left hMassNonzero
  have hDifference : hPlus - hMinus = 0 :=
    sq_eq_zero_iff.mp hSquare
  linarith

/-- Linear mass-matrix action in the plus equation. -/
def massMatrixPlus
    (massSquared hPlus hMinus : ℝ) : ℝ :=
  massSquared * (hPlus - hMinus)

/-- Linear mass-matrix action in the minus equation. -/
def massMatrixMinus
    (massSquared hPlus hMinus : ℝ) : ℝ :=
  massSquared * (hMinus - hPlus)

/-- The diagonal graviton is massless. -/
theorem diagonal_mode_is_massless
    (massSquared h : ℝ) :
    massMatrixPlus massSquared h h = 0 /\
      massMatrixMinus massSquared h h = 0 := by
  constructor <;> simp [massMatrixPlus, massMatrixMinus]

/-- The relative mode `(h,-h)` has eigenvalue `2*m^2`. -/
theorem relative_mode_has_positive_eigenvalue
    (massSquared h : ℝ) :
    massMatrixPlus massSquared h (-h) =
        (2 * massSquared) * h /\
      massMatrixMinus massSquared h (-h) =
        (2 * massSquared) * (-h) := by
  constructor <;> unfold massMatrixPlus massMatrixMinus <;> ring

/-- Positive mass coefficient makes the relative eigenvalue positive. -/
theorem relative_eigenvalue_positive
    (massSquared : ℝ)
    (hMass : 0 < massSquared) :
    0 < 2 * massSquared := by
  positivity

/-- Full reduced quadratic energy with two positive kinetic directions. -/
def totalQuadraticEnergy
    (planckPlusSquared planckMinusSquared massSquared hPlus hMinus : ℝ) : ℝ :=
  positiveSpinTwoKinetic
      planckPlusSquared planckMinusSquared hPlus hMinus +
    relativeModePotential massSquared hPlus hMinus

/--
Two positive Einstein--Hilbert coefficients and a nonnegative relative mass term
give a positive quadratic energy for every nonzero pair of modes.
-/
theorem total_quadratic_energy_positive
    (planckPlusSquared planckMinusSquared massSquared hPlus hMinus : ℝ)
    (hPlanckPlus : 0 < planckPlusSquared)
    (hPlanckMinus : 0 < planckMinusSquared)
    (hMass : 0 ≤ massSquared)
    (hMode : hPlus ≠ 0 ∨ hMinus ≠ 0) :
    0 < totalQuadraticEnergy
      planckPlusSquared planckMinusSquared massSquared hPlus hMinus := by
  unfold totalQuadraticEnergy
  exact add_pos_of_pos_of_nonneg
    (positive_spin_two_kinetic_is_definite
      planckPlusSquared planckMinusSquared hPlus hMinus
      hPlanckPlus hPlanckMinus hMode)
    (relative_mode_potential_nonnegative
      massSquared hPlus hMinus hMass)

/--
The selected PT-flat coefficient cone supplies the positive relative mass
coefficient required by the linear spectrum theorem.
-/
theorem pt_flat_coefficients_supply_safe_linear_mass
    (beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2) :
    0 < fpMassCombination (ptFlatCoefficients beta1 beta2) :=
  pt_flat_fp_mass_positive beta1 beta2 hBeta1 hBeta2

/--
This closes the homogeneous quadratic spectrum.  The full tensor/vector/scalar
constraint analysis and the absence of the nonlinear Boulware--Deser mode still
require the complete covariant action.
-/
structure LinearSpectrumClosureStatus where
  positiveEinsteinHilbertCoefficients : Prop
  diagonalMasslessModeDerived : Prop
  relativeMassiveModeDerived : Prop
  relativeMassSquaredPositive : Prop
  quadraticHamiltonianPositive : Prop
  vectorConstraintClosed : Prop
  scalarConstraintClosed : Prop
  nonlinearSecondaryConstraintClosed : Prop


def fullSpectrumClosure (s : LinearSpectrumClosureStatus) : Prop :=
  s.positiveEinsteinHilbertCoefficients /\
  s.diagonalMasslessModeDerived /\
  s.relativeMassiveModeDerived /\
  s.relativeMassSquaredPositive /\
  s.quadraticHamiltonianPositive /\
  s.vectorConstraintClosed /\
  s.scalarConstraintClosed /\
  s.nonlinearSecondaryConstraintClosed

end P0EFTJanusPositiveBimetricLinearSpectrum
end JanusFormal
