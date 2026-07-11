import Mathlib

namespace JanusFormal
namespace P0EFTJanusHolonomyDeterminantNoGo

set_option autoImplicit false

/--
After subtracting the local term linear in `x = mass * circumference`, the
one-dimensional determinant with holonomy phase `theta` has the dimensionless
factor

`1 - 2*cos(theta)*r + r^2`, where `r = exp(-x)`.

The infinite-product/zeta derivation of this formula remains an analytic input;
the stationarity algebra below is exact once the formula is supplied.
-/
def holonomyDeterminantFactor
    (cosPhase radial : ℝ) : ℝ :=
  1 - 2 * cosPhase * radial + radial ^ 2

/-- Numerator of the logarithmic derivative with respect to `x`. -/
def holonomyDerivativeNumerator
    (cosPhase radial : ℝ) : ℝ :=
  2 * radial * (cosPhase - radial)

/-- Useful square decomposition of the determinant factor. -/
theorem holonomy_factor_square_decomposition
    (cosPhase radial : ℝ) :
    holonomyDeterminantFactor cosPhase radial =
      (radial - cosPhase) ^ 2 + (1 - cosPhase ^ 2) := by
  unfold holonomyDeterminantFactor
  ring

/-- For a nontrivial phase with `cos^2(theta)<1`, the determinant factor is positive. -/
theorem holonomy_factor_positive
    (cosPhase radial : ℝ)
    (hPhase : cosPhase ^ 2 < 1) :
    0 < holonomyDeterminantFactor cosPhase radial := by
  rw [holonomy_factor_square_decomposition]
  have hSquare : 0 ≤ (radial - cosPhase) ^ 2 := sq_nonneg _
  nlinarith

/-- At positive radial variable, stationarity occurs exactly at `r=cos(theta)`. -/
theorem holonomy_stationary_iff_radial_eq_cosine
    (cosPhase radial : ℝ)
    (hRadial : 0 < radial) :
    holonomyDerivativeNumerator cosPhase radial = 0 ↔
      radial = cosPhase := by
  constructor
  · intro hZero
    unfold holonomyDerivativeNumerator at hZero
    have hFactor : 2 * radial ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt hRadial)
    have hDifference : cosPhase - radial = 0 :=
      (mul_eq_zero.mp hZero).resolve_left hFactor
    linarith
  · intro hEqual
    rw [hEqual]
    simp [holonomyDerivativeNumerator]

/-- Below the stationary radial value, the logarithmic derivative numerator is positive. -/
theorem holonomy_derivative_positive_below_cosine
    (cosPhase radial : ℝ)
    (hRadial : 0 < radial)
    (hBelow : radial < cosPhase) :
    0 < holonomyDerivativeNumerator cosPhase radial := by
  unfold holonomyDerivativeNumerator
  exact mul_pos
    (mul_pos (by norm_num) hRadial)
    (sub_pos.mpr hBelow)

/-- Above the stationary radial value, the logarithmic derivative numerator is negative. -/
theorem holonomy_derivative_negative_above_cosine
    (cosPhase radial : ℝ)
    (hRadial : 0 < radial)
    (hAbove : cosPhase < radial) :
    holonomyDerivativeNumerator cosPhase radial < 0 := by
  unfold holonomyDerivativeNumerator
  exact mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) hRadial)
    (sub_neg.mpr hAbove)

/-- Exact quarter holonomy has `cos(theta)=0`. -/
def quarterHolonomyCosine : ℝ := 0

/-- The quarter-holonomy determinant factor is `1+r^2`. -/
theorem quarter_holonomy_factor
    (radial : ℝ) :
    holonomyDeterminantFactor quarterHolonomyCosine radial =
      1 + radial ^ 2 := by
  simp [holonomyDeterminantFactor, quarterHolonomyCosine]

/-- Its logarithmic derivative numerator is strictly negative for every finite positive `r`. -/
theorem quarter_holonomy_derivative_strictly_negative
    (radial : ℝ)
    (hRadial : 0 < radial) :
    holonomyDerivativeNumerator quarterHolonomyCosine radial < 0 := by
  unfold holonomyDerivativeNumerator quarterHolonomyCosine
  nlinarith [sq_pos_of_pos hRadial]

/-- Therefore a single exact-quarter-holonomy tower has no interior stationary modulus. -/
theorem quarter_holonomy_has_no_positive_stationary_radial
    (radial : ℝ)
    (hRadial : 0 < radial) :
    holonomyDerivativeNumerator quarterHolonomyCosine radial ≠ 0 := by
  exact ne_of_lt
    (quarter_holonomy_derivative_strictly_negative radial hRadial)

/-- Periodic holonomy has its formal stationary point only at the boundary `r=1`. -/
theorem periodic_holonomy_stationary_requires_boundary
    (radial : ℝ)
    (hRadial : 0 < radial)
    (hStationary : holonomyDerivativeNumerator 1 radial = 0) :
    radial = 1 := by
  exact (holonomy_stationary_iff_radial_eq_cosine 1 radial hRadial).mp
    hStationary

/-- Antiperiodic holonomy has no positive stationary radial variable. -/
theorem antiperiodic_holonomy_has_no_positive_stationary
    (radial : ℝ)
    (hRadial : 0 < radial) :
    holonomyDerivativeNumerator (-1) radial ≠ 0 := by
  intro hZero
  have hEqual :=
    (holonomy_stationary_iff_radial_eq_cosine (-1) radial hRadial).mp
      hZero
  nlinarith

/--
A phase with `0<cos(theta)<1` is the only single-tower case admitting an
interior stationary radial variable `r=cos(theta)`.  The exact `Z4` quarter
phase sits at the endpoint `cos(theta)=0`, so it cannot by itself stabilize the
mapping-torus circle through the determinant magnitude.
-/
structure HolonomyDeterminantPhysicalStatus where
  zetaRegularizedCircleProductDerived : Prop
  localLinearCountertermSubtracted : Prop
  quarterHolonomyDerivedFromGlobalPinLift : Prop
  completeSphereTowerIncluded : Prop
  bosonFermionAndGhostSignsIncluded : Prop
  competingHolonomySectorsIncluded : Prop
  interactingEffectiveActionDerived : Prop
  finiteCircleMinimumDerived : Prop


def holonomyDeterminantPhysicalClosure
    (s : HolonomyDeterminantPhysicalStatus) : Prop :=
  s.zetaRegularizedCircleProductDerived /\
  s.localLinearCountertermSubtracted /\
  s.quarterHolonomyDerivedFromGlobalPinLift /\
  s.completeSphereTowerIncluded /\
  s.bosonFermionAndGhostSignsIncluded /\
  s.competingHolonomySectorsIncluded /\
  s.interactingEffectiveActionDerived /\
  s.finiteCircleMinimumDerived

end P0EFTJanusHolonomyDeterminantNoGo
end JanusFormal
