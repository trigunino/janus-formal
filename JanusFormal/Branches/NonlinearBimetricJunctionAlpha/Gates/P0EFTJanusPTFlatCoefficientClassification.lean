import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusPTFlatCoefficientClassification

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- First derivative of the proportional potential evaluated at `c = 1`. -/
def proportionalPotentialDerivativeAtOne
    (b : PotentialCoefficients) : ℝ :=
  4 * b.beta1 + 12 * b.beta2 +
    12 * b.beta3 + 4 * b.beta4

/-- Curvature of the interaction energy `-V` at `c = 1`. -/
def interactionEnergyCurvatureAtOne
    (b : PotentialCoefficients) : ℝ :=
  -(12 * b.beta2 + 24 * b.beta3 + 12 * b.beta4)

/--
PT symmetry and vanishing proportional vacuum energy force the complete
coefficient classification

`beta4 = beta0`, `beta3 = beta1`, `beta0 = -4 beta1 - 3 beta2`.
-/
theorem pt_symmetry_and_flatness_classify_coefficients
    (b : PotentialCoefficients)
    (hPT : PTSymmetric b)
    (hFlat : proportionalPotential b 1 = 0) :
    b.beta0 = -4 * b.beta1 - 3 * b.beta2 /\
      b.beta4 = -4 * b.beta1 - 3 * b.beta2 /\
      b.beta3 = b.beta1 := by
  rcases hPT with ⟨h04, h13⟩
  unfold proportionalPotential at hFlat
  norm_num at hFlat
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · exact h13.symm

/-- The classified flat point is automatically stationary. -/
theorem pt_flat_point_is_stationary
    (b : PotentialCoefficients)
    (hPT : PTSymmetric b)
    (hFlat : proportionalPotential b 1 = 0) :
    proportionalPotentialDerivativeAtOne b = 0 := by
  rcases pt_symmetry_and_flatness_classify_coefficients b hPT hFlat with
    ⟨hBeta0, hBeta4, hBeta3⟩
  unfold proportionalPotentialDerivativeAtOne
  rw [hBeta4, hBeta3]
  ring

/-- The interaction-energy curvature is exactly `24*(beta1+beta2)`. -/
theorem classified_interaction_curvature
    (b : PotentialCoefficients)
    (hPT : PTSymmetric b)
    (hFlat : proportionalPotential b 1 = 0) :
    interactionEnergyCurvatureAtOne b =
      24 * (b.beta1 + b.beta2) := by
  rcases pt_symmetry_and_flatness_classify_coefficients b hPT hFlat with
    ⟨_hBeta0, hBeta4, hBeta3⟩
  unfold interactionEnergyCurvatureAtOne
  rw [hBeta4, hBeta3]
  ring

/-- Positive `beta1` and nonnegative `beta2` give a strict local minimum. -/
theorem classified_flat_branch_has_positive_curvature
    (b : PotentialCoefficients)
    (hPT : PTSymmetric b)
    (hFlat : proportionalPotential b 1 = 0)
    (hBeta1 : 0 < b.beta1)
    (hBeta2 : 0 ≤ b.beta2) :
    0 < interactionEnergyCurvatureAtOne b := by
  rw [classified_interaction_curvature b hPT hFlat]
  positivity

/--
Conversely, the explicit two-parameter family exhausts all PT-symmetric flat
proportional coefficients component by component.
-/
theorem explicit_family_matches_classified_coefficients
    (b : PotentialCoefficients)
    (hPT : PTSymmetric b)
    (hFlat : proportionalPotential b 1 = 0) :
    b.beta0 = (ptFlatCoefficients b.beta1 b.beta2).beta0 /\
      b.beta1 = (ptFlatCoefficients b.beta1 b.beta2).beta1 /\
      b.beta2 = (ptFlatCoefficients b.beta1 b.beta2).beta2 /\
      b.beta3 = (ptFlatCoefficients b.beta1 b.beta2).beta3 /\
      b.beta4 = (ptFlatCoefficients b.beta1 b.beta2).beta4 := by
  rcases pt_symmetry_and_flatness_classify_coefficients b hPT hFlat with
    ⟨hBeta0, hBeta4, hBeta3⟩
  simp [ptFlatCoefficients, hBeta0, hBeta3, hBeta4]

/--
This classifies the proportional potential, but the full nonlinear completion
still requires the matrix square-root branch, Hassan--Rosen constraints, matter
couplings and null-boundary variational principle.
-/
structure CoefficientClassificationStatus where
  ptSymmetryDerived : Prop
  flatVacuumConditionDerived : Prop
  coefficientsClassified : Prop
  stationaryPointDerived : Prop
  positiveCurvatureConeSelected : Prop
  squareRootBranchDefined : Prop
  nonlinearGhostConstraintClosed : Prop


def coefficientClassificationClosed
    (s : CoefficientClassificationStatus) : Prop :=
  s.ptSymmetryDerived /\
  s.flatVacuumConditionDerived /\
  s.coefficientsClassified /\
  s.stationaryPointDerived /\
  s.positiveCurvatureConeSelected /\
  s.squareRootBranchDefined /\
  s.nonlinearGhostConstraintClosed

end P0EFTJanusPTFlatCoefficientClassification
end JanusFormal
