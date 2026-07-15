import Mathlib

namespace JanusFormal
namespace P0EFTJanusLambda3CubicGalileon

set_option autoImplicit false

noncomputable def cubicEOM
    (betaHat1 betaHat2 traceSquared contractionSquared : ℝ) : ℝ :=
  betaHat1 * (traceSquared - contractionSquared) +
    (3 / 2 : ℝ) * betaHat2 * (contractionSquared - traceSquared)

theorem cubic_eom_factors_as_galileon
    (betaHat1 betaHat2 traceSquared contractionSquared : ℝ) :
    cubicEOM betaHat1 betaHat2 traceSquared contractionSquared =
      (betaHat1 - (3 / 2 : ℝ) * betaHat2) *
        (traceSquared - contractionSquared) := by
  unfold cubicEOM
  ring

theorem spherical_u2_factorization (radial tangential : ℝ) :
    (radial + 2 * tangential) ^ 2 -
        (radial ^ 2 + 2 * tangential ^ 2) =
      2 * tangential * (2 * radial + tangential) := by
  ring

end P0EFTJanusLambda3CubicGalileon
end JanusFormal
