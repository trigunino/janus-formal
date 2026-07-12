import Mathlib

namespace JanusFormal
namespace P0EFTJanusExactCoshNormalizationAudit

set_option autoImplicit false

/--
Algebraic jet data extracted from the parametric exact solution

`a(u) = A * cosh(u)^2`,
`t(u) = A / c * (1 + sinh(2*u)/2 + u)`.

Direct differentiation gives `a^2 * d^2a/dt^2 = A*c^2/2`.  We record the
cleared-denominator identity here so that the source-normalization audit is a
small, stable algebraic theorem.  The accompanying Python audit differentiates
the parametric functions symbolically.
-/
structure ExactCoshJet where
  alphaSquaredLength : ℝ
  lightSpeed : ℝ
  aSquaredAcceleration : ℝ
  parametricJetIdentity :
    2 * aSquaredAcceleration = alphaSquaredLength * lightSpeed ^ 2

/--
The normalization printed in D'Agostini--Petit 2018, Eq. (11), written without
division:

`3*c^2*A = -8*pi*G*E`.
-/
structure M18Normalization extends ExactCoshJet where
  piConstant : ℝ
  gravitationalConstant : ℝ
  globalEnergy : ℝ
  sourceScaleLaw :
    3 * lightSpeed ^ 2 * alphaSquaredLength =
      -8 * piConstant * gravitationalConstant * globalEnergy

/--
The parametric solution together with Eq. (11) satisfies the coefficient
`4*pi*G/3`, not `8*pi*G/3`, in the acceleration equation.
-/
theorem m18_scale_law_forces_four_pi_equation
    (s : M18Normalization) :
    3 * s.aSquaredAcceleration +
      4 * s.piConstant * s.gravitationalConstant * s.globalEnergy = 0 := by
  nlinarith [s.parametricJetIdentity, s.sourceScaleLaw]

/--
The residual obtained by inserting the same parametric solution and Eq. (11)
into the displayed Eq. (9) is exactly `4*pi*G*E`.
-/
theorem m18_displayed_eight_pi_residual
    (s : M18Normalization) :
    3 * s.aSquaredAcceleration +
        8 * s.piConstant * s.gravitationalConstant * s.globalEnergy =
      4 * (s.piConstant * s.gravitationalConstant * s.globalEnergy) := by
  nlinarith [s.parametricJetIdentity, s.sourceScaleLaw]

/-- Therefore the displayed `8*pi/3` equation cannot hold for a nonzero source. -/
theorem m18_displayed_eight_pi_equation_incompatible_with_nonzero_source
    (s : M18Normalization)
    (hSource :
      s.piConstant * s.gravitationalConstant * s.globalEnergy ≠ 0) :
    3 * s.aSquaredAcceleration +
        8 * s.piConstant * s.gravitationalConstant * s.globalEnergy ≠ 0 := by
  rw [m18_displayed_eight_pi_residual s]
  exact mul_ne_zero (by norm_num) hSource

/--
A source convention is safe to use downstream only after its density, energy,
time-coordinate, and coefficient conventions have been kept together.
-/
structure SourceConventionSeparation where
  m18MassDensityConventionTracked : Prop
  m18AlphaSquaredLengthConventionTracked : Prop
  epjc2024EnergyDensityConventionTracked : Prop
  epjc2024X0DerivativeConventionTracked : Prop
  crossPaperNormalizationMapDerived : Prop
  silentConventionMixingForbidden : Prop


def conventionAuditClosed (s : SourceConventionSeparation) : Prop :=
  s.m18MassDensityConventionTracked /\
  s.m18AlphaSquaredLengthConventionTracked /\
  s.epjc2024EnergyDensityConventionTracked /\
  s.epjc2024X0DerivativeConventionTracked /\
  s.crossPaperNormalizationMapDerived /\
  s.silentConventionMixingForbidden

end P0EFTJanusExactCoshNormalizationAudit
end JanusFormal
