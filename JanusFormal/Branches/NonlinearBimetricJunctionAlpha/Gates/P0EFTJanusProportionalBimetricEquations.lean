import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusProportionalBimetricEquations

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Mixed endomorphism `g⁻¹ f = c² I` on a proportional branch. -/
def proportionalMixedMap {ι : Type}
    (c : ℝ) (vector : ι → ℝ) : ι → ℝ :=
  fun index => c ^ 2 * vector index

/-- Real square-root branch `X = c I`. -/
def proportionalSquareRoot {ι : Type}
    (c : ℝ) (vector : ι → ℝ) : ι → ℝ :=
  fun index => c * vector index

/-- The candidate root squares exactly to the proportional mixed map. -/
theorem proportional_square_root_squares_to_mixed_map {ι : Type}
    (c : ℝ) (vector : ι → ℝ) :
    proportionalSquareRoot c (proportionalSquareRoot c vector) =
      proportionalMixedMap c vector := by
  funext index
  unfold proportionalSquareRoot proportionalMixedMap
  ring

/-- Positive proportional ratio selects a positive real root eigenvalue. -/
theorem positive_ratio_selects_positive_real_square_root
    (c : ℝ) (hC : 0 < c) :
    0 < c ∧ c ^ 2 ≠ 0 := by
  exact ⟨hC, pow_ne_zero 2 (ne_of_gt hC)⟩

/-- Metric exchange sends the positive root ratio to its reciprocal. -/
theorem exchanged_positive_root_is_reciprocal
    (c : ℝ) (hC : 0 < c) :
    0 < 1 / c ∧ c * (1 / c) = 1 := by
  constructor
  · exact one_div_pos.mpr hC
  · simpa [div_eq_mul_inv] using mul_inv_cancel₀ (ne_of_gt hC)

/-- Reduced `g`-sector algebraic equation on a proportional branch `f=c^2 g`. -/
def plusBranchEquation
    (b : PotentialCoefficients) (c : ℝ) : ℝ :=
  b.beta0 + 3 * b.beta1 * c + 3 * b.beta2 * c ^ 2 +
    b.beta3 * c ^ 3

/-- Reduced `f`-sector algebraic equation in the reciprocal convention. -/
def minusBranchEquation
    (b : PotentialCoefficients) (c : ℝ) : ℝ :=
  b.beta4 * c ^ 3 + 3 * b.beta3 * c ^ 2 +
    3 * b.beta2 * c + b.beta1

/-- The PT-flat coefficient family solves both flat equations at `c=1`. -/
theorem pt_flat_solves_both_branch_equations
    (beta1 beta2 : ℝ) :
    plusBranchEquation (ptFlatCoefficients beta1 beta2) 1 = 0 /\
      minusBranchEquation (ptFlatCoefficients beta1 beta2) 1 = 0 := by
  constructor
  · unfold plusBranchEquation ptFlatCoefficients
    ring
  · unfold minusBranchEquation ptFlatCoefficients
    ring

/-- Bianchi factor multiplying the relative Hubble/connection branch. -/
def bianchiFactor
    (b : PotentialCoefficients) (c : ℝ) : ℝ :=
  b.beta1 + 2 * b.beta2 * c + b.beta3 * c ^ 2

/-- Algebraic derivative of the plus-sector FLRW interaction density. -/
def plusBranchEquationDerivative
    (b : PotentialCoefficients) (c : ℝ) : ℝ :=
  3 * b.beta1 + 6 * b.beta2 * c + 3 * b.beta3 * c ^ 2

/-- The density derivative is exactly three times the Bianchi factor. -/
theorem interaction_density_derivative_is_bianchi_factor
    (b : PotentialCoefficients) (c : ℝ) :
    plusBranchEquationDerivative b c = 3 * bianchiFactor b c := by
  unfold plusBranchEquationDerivative bianchiFactor
  ring

/-- Ratio evolution on a common-time FLRW branch. -/
def ratioEvolution (ratio plusExpansion minusExpansion : ℝ) : ℝ :=
  ratio * (minusExpansion - plusExpansion)

/-- Reduced covariant-continuity residual of the interaction density. -/
def interactionContinuityResidual
    (b : PotentialCoefficients)
    (ratio plusExpansion minusExpansion : ℝ) : ℝ :=
  plusBranchEquationDerivative b ratio *
    ratioEvolution ratio plusExpansion minusExpansion

/-- Exact factorization of the cosmological Bianchi residual. -/
theorem interaction_continuity_residual_factorization
    (b : PotentialCoefficients)
    (ratio plusExpansion minusExpansion : ℝ) :
    interactionContinuityResidual b ratio plusExpansion minusExpansion =
      3 * ratio * bianchiFactor b ratio *
        (minusExpansion - plusExpansion) := by
  unfold interactionContinuityResidual ratioEvolution
  rw [interaction_density_derivative_is_bianchi_factor]
  ring

/-- Positive ratio and nonzero Bianchi factor lock the FLRW expansions. -/
theorem covariant_continuity_locks_expansions
    (b : PotentialCoefficients)
    (ratio plusExpansion minusExpansion : ℝ)
    (hRatio : 0 < ratio)
    (hFactor : bianchiFactor b ratio ≠ 0)
    (hContinuity :
      interactionContinuityResidual b ratio plusExpansion minusExpansion = 0) :
    plusExpansion = minusExpansion := by
  rw [interaction_continuity_residual_factorization] at hContinuity
  have hRatioNonzero : ratio ≠ 0 := ne_of_gt hRatio
  have hCoefficient : 3 * ratio * bianchiFactor b ratio ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hRatioNonzero) hFactor
  have hDifference : minusExpansion - plusExpansion = 0 :=
    (mul_eq_zero.mp hContinuity).resolve_left hCoefficient
  linarith

/-- On the symmetric branch, the factor is the positive Fierz--Pauli combination. -/
theorem pt_flat_bianchi_factor_at_one
    (beta1 beta2 : ℝ) :
    bianchiFactor (ptFlatCoefficients beta1 beta2) 1 =
      2 * (beta1 + beta2) := by
  unfold bianchiFactor ptFlatCoefficients
  ring

/-- The selected coefficient cone keeps the Bianchi factor nonzero. -/
theorem pt_flat_bianchi_factor_positive
    (beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2) :
    0 < bianchiFactor (ptFlatCoefficients beta1 beta2) 1 := by
  rw [pt_flat_bianchi_factor_at_one]
  nlinarith

/-- Reduced dynamical Bianchi constraint. -/
structure ProportionalBianchiConstraint where
  coefficients : PotentialCoefficients
  ratio : ℝ
  plusExpansion : ℝ
  minusExpansion : ℝ
  constraintLaw :
    bianchiFactor coefficients ratio *
      (plusExpansion - minusExpansion) = 0

/-- A nonzero algebraic factor forces the two proportional expansions to agree. -/
theorem nonzero_bianchi_factor_locks_expansions
    (s : ProportionalBianchiConstraint)
    (hFactor : bianchiFactor s.coefficients s.ratio ≠ 0) :
    s.plusExpansion = s.minusExpansion := by
  have hDifference : s.plusExpansion - s.minusExpansion = 0 :=
    (mul_eq_zero.mp s.constraintLaw).resolve_left hFactor
  linarith

/-- In the positive PT-flat cone, the proportional branch is dynamically locked. -/
theorem pt_flat_bianchi_locks_expansions
    (beta1 beta2 plusExpansion minusExpansion : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hConstraint :
      bianchiFactor (ptFlatCoefficients beta1 beta2) 1 *
        (plusExpansion - minusExpansion) = 0) :
    plusExpansion = minusExpansion := by
  have hFactorPositive :=
    pt_flat_bianchi_factor_positive beta1 beta2 hBeta1 hBeta2
  have hFactorNonzero :
      bianchiFactor (ptFlatCoefficients beta1 beta2) 1 ≠ 0 :=
    ne_of_gt hFactorPositive
  have hDifference : plusExpansion - minusExpansion = 0 :=
    (mul_eq_zero.mp hConstraint).resolve_left hFactorNonzero
  linarith

/--
The proportional branch is now algebraically fixed, but a complete spacetime
solution still requires the tensor equations, matter sources and null junction.
-/
structure ProportionalBranchClosureStatus where
  matrixSquareRootExists : Prop
  bothFlatEquationsDerived : Prop
  ptCoefficientConeSelected : Prop
  bianchiFactorPositive : Prop
  expansionLockDerived : Prop
  tensorPerturbationSpectrumStable : Prop
  matterSourceSignsRecovered : Prop
  nullBoundaryMatched : Prop


def proportionalBranchClosed
    (s : ProportionalBranchClosureStatus) : Prop :=
  s.matrixSquareRootExists /\
  s.bothFlatEquationsDerived /\
  s.ptCoefficientConeSelected /\
  s.bianchiFactorPositive /\
  s.expansionLockDerived /\
  s.tensorPerturbationSpectrumStable /\
  s.matterSourceSignsRecovered /\
  s.nullBoundaryMatched

end P0EFTJanusProportionalBimetricEquations
end JanusFormal
