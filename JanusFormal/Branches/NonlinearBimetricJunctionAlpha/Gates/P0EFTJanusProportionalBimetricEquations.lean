import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusProportionalBimetricEquations

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusPTSymmetricFlatBimetricBranch

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
  constructor <;>
    unfold plusBranchEquation minusBranchEquation ptFlatCoefficients <;>
    ring

/-- Bianchi factor multiplying the relative Hubble/connection branch. -/
def bianchiFactor
    (b : PotentialCoefficients) (c : ℝ) : ℝ :=
  b.beta1 + 2 * b.beta2 * c + b.beta3 * c ^ 2

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
