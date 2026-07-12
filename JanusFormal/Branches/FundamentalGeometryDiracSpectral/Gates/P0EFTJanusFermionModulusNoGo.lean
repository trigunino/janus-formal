import Mathlib

namespace JanusFormal
namespace P0EFTJanusFermionModulusNoGo

set_option autoImplicit false

/--
After removing the holonomy-independent local factor from the half-holonomy
mode kernel, a massive product-Dirac pair contributes `(1+exp(-x))^2`, where
`x` is the positive circle length times the sphere eigenvalue.
-/
noncomputable def halfHolonomyFiniteFactor (x : ℝ) : ℝ :=
  (1 + Real.exp (-x)) ^ 2

/-- The unsquared elementary factor is strictly decreasing. -/
theorem elementary_factor_strictly_decreases
    (x y : ℝ)
    (hxy : x < y) :
    1 + Real.exp (-y) < 1 + Real.exp (-x) := by
  have hNeg : -y < -x := neg_lt_neg hxy
  have hExp : Real.exp (-y) < Real.exp (-x) :=
    Real.exp_lt_exp.mpr hNeg
  linarith

/-- The renormalized positive mode factor is strictly decreasing. -/
theorem half_holonomy_finite_factor_strictly_decreases
    (x y : ℝ)
    (hxy : x < y) :
    halfHolonomyFiniteFactor y < halfHolonomyFiniteFactor x := by
  unfold halfHolonomyFiniteFactor
  have hBase := elementary_factor_strictly_decreases x y hxy
  have hYPositive : 0 < 1 + Real.exp (-y) := by
    have hExp : 0 < Real.exp (-y) := Real.exp_pos _
    linarith
  have hXPositive : 0 < 1 + Real.exp (-x) := by
    have hExp : 0 < Real.exp (-x) := Real.exp_pos _
    linarith
  nlinarith [hBase]

/-- Multiplying the circle modulus by a positive eigenvalue preserves ordering. -/
theorem positive_mode_argument_orders_with_modulus
    (eigenvalue modulus₁ modulus₂ : ℝ)
    (hEigenvalue : 0 < eigenvalue)
    (hModulus : modulus₁ < modulus₂) :
    eigenvalue * modulus₁ < eigenvalue * modulus₂ :=
  mul_lt_mul_of_pos_left hModulus hEigenvalue

/-- Every positive massive mode decreases as the circle modulus grows. -/
theorem every_massive_mode_decreases_with_circle_modulus
    (eigenvalue modulus₁ modulus₂ : ℝ)
    (hEigenvalue : 0 < eigenvalue)
    (hModulus : modulus₁ < modulus₂) :
    halfHolonomyFiniteFactor (eigenvalue * modulus₂) <
      halfHolonomyFiniteFactor (eigenvalue * modulus₁) := by
  apply half_holonomy_finite_factor_strictly_decreases
  exact positive_mode_argument_orders_with_modulus
    eigenvalue modulus₁ modulus₂ hEigenvalue hModulus

/--
The pure massless fermion determinant can select the combined holonomy but has
no internal finite-modulus stationary point in its massive nonlocal factors.
A competing contribution with different modulus dependence is required.
-/
structure ModulusStabilizationExitStatus where
  pureFermionMonotonicityProved : Prop
  bosonicDeterminantIncluded : Prop
  classicalGeometricPotentialIncluded : Prop
  llTensionContributionIncluded : Prop
  bimetricBoundaryContributionIncluded : Prop
  interactingGapEquationIncluded : Prop
  atLeastOneCompetingSectorActive : Prop
  finiteStableModulusDerived : Prop


def modulusStabilizationExited
    (s : ModulusStabilizationExitStatus) : Prop :=
  s.pureFermionMonotonicityProved /\
  (s.bosonicDeterminantIncluded \/
    s.classicalGeometricPotentialIncluded \/
    s.llTensionContributionIncluded \/
    s.bimetricBoundaryContributionIncluded \/
    s.interactingGapEquationIncluded) /\
  s.atLeastOneCompetingSectorActive /\
  s.finiteStableModulusDerived

end P0EFTJanusFermionModulusNoGo
end JanusFormal
