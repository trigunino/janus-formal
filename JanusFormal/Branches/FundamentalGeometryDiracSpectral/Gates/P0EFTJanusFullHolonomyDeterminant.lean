import Mathlib

namespace JanusFormal
namespace P0EFTJanusFullHolonomyDeterminant

set_option autoImplicit false

/--
Holonomy-dependent factor obtained by zeta-regularizing the circle momentum
product of a product-Dirac mode.  `massAngle` denotes the dimensionless product
of the circle circumference and the nonnegative sphere eigenvalue.
-/
noncomputable def modeDeterminantKernel
    (massAngle holonomy : ℝ) : ℝ :=
  Real.cosh massAngle - Real.cos (2 * Real.pi * holonomy)

/-- The half-holonomy kernel is `cosh(massAngle)+1`. -/
@[simp] theorem mode_kernel_at_half
    (massAngle : ℝ) :
    modeDeterminantKernel massAngle (1 / 2) =
      Real.cosh massAngle + 1 := by
  unfold modeDeterminantKernel
  have hArg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [hArg, Real.cos_pi]
  ring

/--
For any holonomy whose cosine obeys the standard lower bound `-1`, the mode
determinant is no larger than at half holonomy.
-/
theorem mode_kernel_le_half
    (massAngle holonomy : ℝ)
    (hCosLower : -1 ≤ Real.cos (2 * Real.pi * holonomy)) :
    modeDeterminantKernel massAngle holonomy ≤
      modeDeterminantKernel massAngle (1 / 2) := by
  rw [mode_kernel_at_half]
  unfold modeDeterminantKernel
  linarith

/-- The half-holonomy mode kernel is strictly positive. -/
theorem mode_kernel_half_positive
    (massAngle : ℝ) :
    0 < modeDeterminantKernel massAngle (1 / 2) := by
  rw [mode_kernel_at_half]
  have hCosh : 1 ≤ Real.cosh massAngle :=
    Real.one_le_cosh massAngle
  linarith

/--
A product of two positive mode factors remains maximized at half holonomy if
each factor is.
-/
theorem two_mode_product_le_half
    (f₁ f₂ h₁ h₂ : ℝ)
    (hf₁ : 0 ≤ f₁)
    (hf₂ : 0 ≤ f₂)
    (h₁Bound : f₁ ≤ h₁)
    (h₂Bound : f₂ ≤ h₂) :
    f₁ * f₂ ≤ h₁ * h₂ := by
  have hh₁ : 0 ≤ h₁ := le_trans hf₁ h₁Bound
  exact mul_le_mul h₁Bound h₂Bound hf₂ hh₁

/--
The regularized circle-product identity to be proved analytically for every
sphere eigenvalue is

`Prod_k [((2*pi*(k+a))/beta)^2 + lambda^2]
   = C(lambda,beta) * 2*(cosh(beta*lambda)-cos(2*pi*a))`,

where `C` is holonomy independent.  Once this identity and positivity are
proved, every spectral level selects half holonomy simultaneously.
-/
structure FullDeterminantClosureStatus where
  circleProductZetaRegularized : Prop
  modeKernelFormulaDerived : Prop
  modeMultiplicitiesIncluded : Prop
  infiniteModeProductConverges : Prop
  localCountertermsHolonomyIndependent : Prop
  determinantPositiveOnFundamentalDomain : Prop
  halfHolonomyGlobalMaximumProved : Prop
  effectiveActionGlobalMinimumProved : Prop
  etaPhaseCombinedConsistently : Prop


def fullDeterminantClosure
    (s : FullDeterminantClosureStatus) : Prop :=
  s.circleProductZetaRegularized /\
  s.modeKernelFormulaDerived /\
  s.modeMultiplicitiesIncluded /\
  s.infiniteModeProductConverges /\
  s.localCountertermsHolonomyIndependent /\
  s.determinantPositiveOnFundamentalDomain /\
  s.halfHolonomyGlobalMaximumProved /\
  s.effectiveActionGlobalMinimumProved /\
  s.etaPhaseCombinedConsistently

end P0EFTJanusFullHolonomyDeterminant
end JanusFormal
