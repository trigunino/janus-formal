import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianPitchforkBifurcation4D

/-!
# Quartic potential behind the scalar pitchfork normal form

The reduced pitchfork Euler map

`a * (mu + c a^2)`

is the derivative of the quartic potential

`V(mu,a) = 1/2 mu a^2 + 1/4 c a^4`.

This file proves the derivative and Hessian formulas and classifies the local
stability of the trivial and nontrivial branches.  For `c>0`, the broken
branches at `mu<0` are strict local minima, while the trivial branch changes
from stable to unstable at `mu=0`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarPitchforkPotential4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarLagrangianPitchforkBifurcation4D

/-- Quartic pitchfork potential. -/
def canonicalScalarPitchforkPotential
    (cubic parameter amplitude : Real) : Real :=
  (1 / 2 : Real) * parameter * amplitude ^ 2 +
    (1 / 4 : Real) * cubic * amplitude ^ 4

/-- First derivative of the quartic potential. -/
theorem canonicalScalarPitchforkPotential_hasDerivAt
    (cubic parameter amplitude : Real) :
    HasDerivAt
      (canonicalScalarPitchforkPotential cubic parameter)
      (canonicalScalarPitchforkReducedEuler cubic parameter amplitude)
      amplitude := by
  unfold canonicalScalarPitchforkPotential
    canonicalScalarPitchforkReducedEuler
  convert ((((hasDerivAt_const (x := amplitude) ((1 / 2 : Real) * parameter)).mul
      ((hasDerivAt_id amplitude).pow 2)).add
    ((hasDerivAt_const (x := amplitude) ((1 / 4 : Real) * cubic)).mul
      ((hasDerivAt_id amplitude).pow 4)))) using 1 <;> ring

/-- Algebraic Hessian of the quartic potential. -/
def canonicalScalarPitchforkHessian
    (cubic parameter amplitude : Real) : Real :=
  parameter + 3 * cubic * amplitude ^ 2

/-- Derivative of the reduced Euler map equals the Hessian. -/
theorem canonicalScalarPitchforkReducedEuler_hasDerivAt
    (cubic parameter amplitude : Real) :
    HasDerivAt
      (canonicalScalarPitchforkReducedEuler cubic parameter)
      (canonicalScalarPitchforkHessian cubic parameter amplitude)
      amplitude := by
  unfold canonicalScalarPitchforkReducedEuler
    canonicalScalarPitchforkHessian
  convert ((hasDerivAt_id amplitude).mul
    ((hasDerivAt_const (x := amplitude) parameter).add
      ((hasDerivAt_const (x := amplitude) cubic).mul
        ((hasDerivAt_id amplitude).pow 2)))) using 1 <;> ring

/-- The trivial branch Hessian is the control parameter. -/
@[simp] theorem canonicalScalarPitchforkHessian_zero
    (cubic parameter : Real) :
    canonicalScalarPitchforkHessian cubic parameter 0 = parameter := by
  simp [canonicalScalarPitchforkHessian]

/-- Hessian on a nontrivial critical point. -/
theorem canonicalScalarPitchforkHessian_of_nonzero_critical
    (cubic parameter amplitude : Real)
    (hAmplitude : amplitude ≠ 0)
    (hCritical : canonicalScalarPitchforkReducedEuler
      cubic parameter amplitude = 0) :
    canonicalScalarPitchforkHessian cubic parameter amplitude =
      2 * cubic * amplitude ^ 2 := by
  have hEquation := (canonicalScalarPitchforkReducedEuler_eq_zero_iff
    cubic parameter amplitude).1 hCritical
  rcases hEquation with hZero | hEquation
  · exact False.elim (hAmplitude hZero)
  · unfold canonicalScalarPitchforkHessian
    linarith

/-- Equivalent nontrivial Hessian formula `-2 parameter`. -/
theorem canonicalScalarPitchforkHessian_of_nonzero_critical_eq_neg_parameter
    (cubic parameter amplitude : Real)
    (hAmplitude : amplitude ≠ 0)
    (hCritical : canonicalScalarPitchforkReducedEuler
      cubic parameter amplitude = 0) :
    canonicalScalarPitchforkHessian cubic parameter amplitude =
      -2 * parameter := by
  have hEquation := (canonicalScalarPitchforkReducedEuler_eq_zero_iff
    cubic parameter amplitude).1 hCritical
  rcases hEquation with hZero | hEquation
  · exact False.elim (hAmplitude hZero)
  · unfold canonicalScalarPitchforkHessian
    linarith

/-- For positive quartic coefficient and negative parameter, the positive broken
branch has positive Hessian. -/
theorem canonicalScalarPitchforkHessian_sqrt_pos
    (cubic parameter : Real)
    (hCubic : 0 < cubic)
    (hParameter : parameter < 0) :
    0 < canonicalScalarPitchforkHessian cubic parameter
      (Real.sqrt (-parameter / cubic)) := by
  have hRatio : 0 < -parameter / cubic := div_pos (neg_pos.mpr hParameter) hCubic
  have hAmplitude : Real.sqrt (-parameter / cubic) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hRatio)
  have hCritical := canonicalScalarPitchforkReducedEuler_sqrt
    cubic parameter hCubic.ne' hRatio.le
  rw [canonicalScalarPitchforkHessian_of_nonzero_critical_eq_neg_parameter
    cubic parameter _ hAmplitude hCritical]
  linarith

/-- The negative broken branch has the same positive Hessian. -/
theorem canonicalScalarPitchforkHessian_neg_sqrt_pos
    (cubic parameter : Real)
    (hCubic : 0 < cubic)
    (hParameter : parameter < 0) :
    0 < canonicalScalarPitchforkHessian cubic parameter
      (-Real.sqrt (-parameter / cubic)) := by
  have hRatio : 0 < -parameter / cubic := div_pos (neg_pos.mpr hParameter) hCubic
  have hAmplitude : -Real.sqrt (-parameter / cubic) ≠ 0 := by
    exact neg_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hRatio))
  have hCritical := canonicalScalarPitchforkReducedEuler_neg_sqrt
    cubic parameter hCubic.ne' hRatio.le
  rw [canonicalScalarPitchforkHessian_of_nonzero_critical_eq_neg_parameter
    cubic parameter _ hAmplitude hCritical]
  linarith

/-- Potential value on a nontrivial critical point. -/
theorem canonicalScalarPitchforkPotential_of_nonzero_critical
    (cubic parameter amplitude : Real)
    (hCubic : cubic ≠ 0)
    (hAmplitude : amplitude ≠ 0)
    (hCritical : canonicalScalarPitchforkReducedEuler
      cubic parameter amplitude = 0) :
    canonicalScalarPitchforkPotential cubic parameter amplitude =
      -(parameter ^ 2) / (4 * cubic) := by
  have hSquare := (canonicalScalarPitchforkReducedEuler_nonzero_iff_sq
    cubic parameter amplitude hCubic hAmplitude).1 hCritical
  unfold canonicalScalarPitchforkPotential
  rw [hSquare]
  field_simp
  ring

/-- Broken branches lower the potential below the trivial branch for positive
quartic coefficient and negative parameter. -/
theorem canonicalScalarPitchforkPotential_sqrt_lt_zero
    (cubic parameter : Real)
    (hCubic : 0 < cubic)
    (hParameter : parameter < 0) :
    canonicalScalarPitchforkPotential cubic parameter
        (Real.sqrt (-parameter / cubic)) <
      canonicalScalarPitchforkPotential cubic parameter 0 := by
  have hRatio : 0 < -parameter / cubic := div_pos (neg_pos.mpr hParameter) hCubic
  have hAmplitude : Real.sqrt (-parameter / cubic) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hRatio)
  have hCritical := canonicalScalarPitchforkReducedEuler_sqrt
    cubic parameter hCubic.ne' hRatio.le
  rw [canonicalScalarPitchforkPotential_of_nonzero_critical
      cubic parameter _ hCubic.ne' hAmplitude hCritical]
  simp [canonicalScalarPitchforkPotential]
  have hSquare : 0 < parameter ^ 2 := sq_pos_of_ne_zero (ne_of_lt hParameter)
  positivity

/-- Pitchfork-potential certificate. -/
theorem canonicalScalarPitchforkPotential_certificate
    (cubic parameter amplitude : Real) :
    HasDerivAt
        (canonicalScalarPitchforkPotential cubic parameter)
        (canonicalScalarPitchforkReducedEuler cubic parameter amplitude)
        amplitude ∧
      HasDerivAt
        (canonicalScalarPitchforkReducedEuler cubic parameter)
        (canonicalScalarPitchforkHessian cubic parameter amplitude)
        amplitude :=
  ⟨canonicalScalarPitchforkPotential_hasDerivAt cubic parameter amplitude,
    canonicalScalarPitchforkReducedEuler_hasDerivAt cubic parameter amplitude⟩

end
end P0EFTJanusMappingTorusScalarPitchforkPotential4D
end JanusFormal
