import Mathlib

namespace JanusFormal
namespace P0EFTJanusSmoothNotPolynomial

set_option autoImplicit false

/-- Pointwise exponential operation on scalar sections. -/
noncomputable def pointwiseExp
    {Base : Type*}
    (section : Base → ℝ) : Base → ℝ :=
  fun point => Real.exp (section point)

/-- Pointwise exponential commutes with every pullback. -/
theorem pointwise_exp_natural
    {SourceBase TargetBase : Type*}
    (map : SourceBase → TargetBase)
    (section : TargetBase → ℝ) :
    pointwiseExp (section ∘ map) =
      pointwiseExp section ∘ map := by
  rfl

/-- The operation depends only on the value, i.e. the zero jet, at a point. -/
theorem pointwise_exp_factors_through_zero_jet
    {Base : Type*}
    (section : Base → ℝ)
    (point : Base) :
    pointwiseExp section point = Real.exp (section point) := by
  rfl

/-- Forward finite difference with unit step. -/
def forwardDifference (function : ℝ → ℝ) : ℝ → ℝ :=
  fun x => function (x + 1) - function x

/-- Iterated forward difference. -/
def iteratedDifference : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, function => function
  | order + 1, function =>
      forwardDifference (iteratedDifference order function)

/-- Exact finite-difference formula for the exponential. -/
theorem iterated_difference_exp
    (order : ℕ)
    (x : ℝ) :
    iteratedDifference order Real.exp x =
      (Real.exp 1 - 1) ^ order * Real.exp x := by
  induction order generalizing x with
  | zero =>
      simp [iteratedDifference]
  | succ order inductionHypothesis =>
      simp only [iteratedDifference, forwardDifference]
      rw [inductionHypothesis (x + 1),
        inductionHypothesis x, Real.exp_add]
      ring

/-- Necessary finite-difference condition satisfied by every ordinary
polynomial function of some finite degree. -/
def HasFiniteDifferencePolynomialCertificate
    (function : ℝ → ℝ) : Prop :=
  ∃ degree : ℕ,
    ∀ x : ℝ,
      iteratedDifference (degree + 1) function x = 0

/-- The exponential has no finite-difference polynomial certificate. -/
theorem exp_has_no_finite_difference_polynomial_certificate :
    Not (HasFiniteDifferencePolynomialCertificate Real.exp) := by
  rintro ⟨degree, hDifference⟩
  have hExpOneGreater : (1 : ℝ) < Real.exp 1 := by
    have hStrict : Real.exp 0 < Real.exp 1 :=
      Real.exp_lt_exp.mpr (by norm_num)
    simpa using hStrict
  have hBase : Real.exp 1 - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt hExpOneGreater)
  have hNonzero :
      (Real.exp 1 - 1) ^ (degree + 1) * Real.exp 0 ≠ 0 :=
    mul_ne_zero
      (pow_ne_zero _ hBase)
      (Real.exp_ne_zero 0)
  have hZero := hDifference 0
  rw [iterated_difference_exp] at hZero
  exact hNonzero hZero

/-- The strong polynomial version of jet universality already fails for a
trivial scalar bundle and an order-zero natural operation. -/
theorem smooth_local_natural_does_not_imply_polynomial :
    (∀ {SourceBase TargetBase : Type*}
      (map : SourceBase → TargetBase)
      (section : TargetBase → ℝ),
      pointwiseExp (section ∘ map) =
        pointwiseExp section ∘ map) /\
    Not (HasFiniteDifferencePolynomialCertificate Real.exp) := by
  exact ⟨pointwise_exp_natural,
    exp_has_no_finite_difference_polynomial_certificate⟩

/--
The correct target of the classification is therefore a smooth equivariant map
on a finite jet fiber.  Polynomial invariant theory applies only after adding a
polynomial/algebraic dependence hypothesis.
-/
structure PolynomialUpgradeStatus where
  smoothEquivariantJetMapConstructed : Prop
  polynomialDependenceAssumedOrDerived : Prop
  algebraicStructureGroupSpecified : Prop
  polynomialInvariantTheoryApplied : Prop
  smoothNonpolynomialOperationsExcluded : Prop


def polynomialUpgradeClosed
    (s : PolynomialUpgradeStatus) : Prop :=
  s.smoothEquivariantJetMapConstructed /\
  s.polynomialDependenceAssumedOrDerived /\
  s.algebraicStructureGroupSpecified /\
  s.polynomialInvariantTheoryApplied /\
  s.smoothNonpolynomialOperationsExcluded

/-- Missing polynomial dependence blocks a polynomial-classification claim. -/
theorem missing_polynomial_hypothesis_blocks_upgrade
    (s : PolynomialUpgradeStatus)
    (hMissing : Not s.polynomialDependenceAssumedOrDerived) :
    Not (polynomialUpgradeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

end P0EFTJanusSmoothNotPolynomial
end JanusFormal
