import Mathlib

namespace JanusFormal
namespace P0EFTJanusCasimirPlanckScaleAudit

set_option autoImplicit false

/--
A one-scale Casimir ansatz in the 2018 mass convention.  The Casimir law is
stored without division as

`c * L * E_global = -C * hbar`.
-/
structure CasimirMatchedScale where
  length : ℝ
  lightSpeed : ℝ
  piConstant : ℝ
  gravitationalConstant : ℝ
  hbar : ℝ
  casimirCoefficient : ℝ
  globalEnergy : ℝ
  sourceScaleLaw :
    3 * lightSpeed ^ 2 * length =
      -8 * piConstant * gravitationalConstant * globalEnergy
  casimirMassLaw :
    lightSpeed * length * globalEnergy =
      -casimirCoefficient * hbar

/--
Combining the exact-solution scale law with a `1/L` Casimir mass gives

`3*c^3*L^2 = 8*pi*G*C*hbar`.

Thus an order-one topological/anomaly coefficient selects a Planckian scale,
not a cosmological one.
-/
theorem casimir_matching_is_planck_scaled
    (s : CasimirMatchedScale) :
    3 * s.lightSpeed ^ 3 * s.length ^ 2 =
      8 * s.piConstant * s.gravitationalConstant *
        s.casimirCoefficient * s.hbar := by
  calc
    3 * s.lightSpeed ^ 3 * s.length ^ 2 =
        (s.lightSpeed * s.length) *
          (3 * s.lightSpeed ^ 2 * s.length) := by ring
    _ = (s.lightSpeed * s.length) *
          (-8 * s.piConstant * s.gravitationalConstant * s.globalEnergy) := by
          rw [s.sourceScaleLaw]
    _ = -8 * s.piConstant * s.gravitationalConstant *
          (s.lightSpeed * s.length * s.globalEnergy) := by ring
    _ = -8 * s.piConstant * s.gravitationalConstant *
          (-s.casimirCoefficient * s.hbar) := by
          rw [s.casimirMassLaw]
    _ = 8 * s.piConstant * s.gravitationalConstant *
          s.casimirCoefficient * s.hbar := by ring

/-- Planck-length normalization, again stored without division. -/
structure CasimirPlanckComparison extends CasimirMatchedScale where
  planckLength : ℝ
  lightSpeedNonzero : lightSpeed ≠ 0
  planckLengthLaw :
    lightSpeed ^ 3 * planckLength ^ 2 = gravitationalConstant * hbar

/-- The dimensionless radius equation is `3 L^2 = 8*pi*C*l_P^2`. -/
theorem casimir_radius_in_planck_units
    (s : CasimirPlanckComparison) :
    3 * s.length ^ 2 =
      8 * s.piConstant * s.casimirCoefficient * s.planckLength ^ 2 := by
  have hCasimir := casimir_matching_is_planck_scaled s.toCasimirMatchedScale
  have hScaled :
      s.lightSpeed ^ 3 *
        (3 * s.length ^ 2 -
          8 * s.piConstant * s.casimirCoefficient * s.planckLength ^ 2) = 0 := by
    rw [mul_sub]
    rw [mul_assoc, hCasimir]
    rw [mul_assoc]
    rw [s.planckLengthLaw]
    ring
  have hCubic : s.lightSpeed ^ 3 ≠ 0 :=
    pow_ne_zero 3 s.lightSpeedNonzero
  have hBracket := (mul_eq_zero.mp hScaled).resolve_left hCubic
  linarith

/--
The Casimir/anomaly route is complete only if the coefficient is derived from
the Janus field content and is large enough without importing the observed
radius.
-/
structure CasimirScaleClosureStatus where
  janusSpectrumDerived : Prop
  boundaryConditionsDerived : Prop
  renormalizedCoefficientDerived : Prop
  coefficientIndependentOfObservedLength : Prop
  coefficientMagnitudeExplained : Prop
  lorentzianMatchingDerived : Prop
  noFitScaleClosed : Prop

end P0EFTJanusCasimirPlanckScaleAudit
end JanusFormal
